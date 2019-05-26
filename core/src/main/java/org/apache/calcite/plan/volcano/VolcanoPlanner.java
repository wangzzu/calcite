/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to you under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.calcite.plan.volcano;

import org.apache.calcite.avatica.util.Spaces;
import org.apache.calcite.config.CalciteConnectionConfig;
import org.apache.calcite.linq4j.tree.Expressions;
import org.apache.calcite.plan.AbstractRelOptPlanner;
import org.apache.calcite.plan.Context;
import org.apache.calcite.plan.Convention;
import org.apache.calcite.plan.ConventionTraitDef;
import org.apache.calcite.plan.RelOptCost;
import org.apache.calcite.plan.RelOptCostFactory;
import org.apache.calcite.plan.RelOptLattice;
import org.apache.calcite.plan.RelOptListener;
import org.apache.calcite.plan.RelOptMaterialization;
import org.apache.calcite.plan.RelOptMaterializations;
import org.apache.calcite.plan.RelOptPlanner;
import org.apache.calcite.plan.RelOptRule;
import org.apache.calcite.plan.RelOptRuleCall;
import org.apache.calcite.plan.RelOptRuleOperand;
import org.apache.calcite.plan.RelOptSchema;
import org.apache.calcite.plan.RelOptTable;
import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.plan.RelTrait;
import org.apache.calcite.plan.RelTraitDef;
import org.apache.calcite.plan.RelTraitSet;
import org.apache.calcite.prepare.CalcitePrepareImpl;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.RelVisitor;
import org.apache.calcite.rel.convert.Converter;
import org.apache.calcite.rel.convert.ConverterRule;
import org.apache.calcite.rel.externalize.RelWriterImpl;
import org.apache.calcite.rel.metadata.JaninoRelMetadataProvider;
import org.apache.calcite.rel.metadata.RelMetadataProvider;
import org.apache.calcite.rel.metadata.RelMetadataQuery;
import org.apache.calcite.rel.rules.AggregateJoinTransposeRule;
import org.apache.calcite.rel.rules.AggregateProjectMergeRule;
import org.apache.calcite.rel.rules.AggregateRemoveRule;
import org.apache.calcite.rel.rules.CalcRemoveRule;
import org.apache.calcite.rel.rules.FilterJoinRule;
import org.apache.calcite.rel.rules.JoinAssociateRule;
import org.apache.calcite.rel.rules.JoinCommuteRule;
import org.apache.calcite.rel.rules.ProjectRemoveRule;
import org.apache.calcite.rel.rules.SemiJoinRule;
import org.apache.calcite.rel.rules.SortRemoveRule;
import org.apache.calcite.rel.rules.UnionToDistinctRule;
import org.apache.calcite.runtime.Hook;
import org.apache.calcite.sql.SqlExplainLevel;
import org.apache.calcite.util.Litmus;
import org.apache.calcite.util.Pair;
import org.apache.calcite.util.PartiallyOrderedSet;
import org.apache.calcite.util.SaffronProperties;
import org.apache.calcite.util.Util;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.LinkedListMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.Ordering;
import com.google.common.collect.SetMultimap;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * VolcanoPlanner optimizes queries by transforming expressions selectively
 * according to a dynamic programming algorithm.
 */
public class VolcanoPlanner extends AbstractRelOptPlanner {
  //~ Static fields/initializers ---------------------------------------------
  private static final boolean DUMP_GRAPHVIZ =
      Util.getBooleanProperty("calcite.volcano.dump.graphviz", true);
  private static final boolean DUMP_SETS =
      Util.getBooleanProperty("calcite.volcano.dump.sets", true);

  protected static final double COST_IMPROVEMENT = .5;

  //~ Instance fields --------------------------------------------------------

  protected RelSubset root;

  /**
   * If true, the planner keeps applying rules as long as they continue to
   * reduce the cost. If false, the planner terminates as soon as it has found
   * any implementation, no matter how expensive.
   * note：true：只要 rule apply 可以减少 cost，就会一直 apply；
   * note：false：只要找到任何实现就会退出，默认是 true
   */
  protected boolean ambitious = true;

  /**
   * If true, and if {@link #ambitious} is true, the planner waits a finite
   * number of iterations for the cost to improve.
   *
   * note：true：如果 ambitious 也 true，planner 将会等待【有限次数】的迭代以提高成本；
   * note：获取第一个有限 plan 的迭代次数记为 K，之后会设置一个目标 best cost（current best cost * COST_IMPROVEMENT）
   * note：如果在 k 次迭代内不能满足，planner 就会退出，当前的 plan 为 best plan，否则会持续设置一个新目录 cost 进行相应的优化
   * note：false：一直触发 rule，直到 rule queue 为 null；
   * <p>The number of iterations K is equal to the number of iterations
   * required to get the first finite plan. After the first finite plan, it
   * continues to fire rules to try to improve it. The planner sets a target
   * cost of the current best cost multiplied by {@link #COST_IMPROVEMENT}. If
   * it does not meet that cost target within K steps, it quits, and uses the
   * current best plan. If it meets the cost, it sets a new, lower target, and
   * has another K iterations to meet it. And so forth.
   *
   * <p>If false, the planner continues to fire rules until the rule queue is
   * empty.
   */
  protected boolean impatient = false;

  /**
   * Operands that apply to a given class of {@link RelNode}.
   *
   * <p>Any operand can be an 'entry point' to a rule call, when a RelNode is
   * registered which matches the operand. This map allows us to narrow down
   * operands based on the class of the RelNode.</p>
   *
   * note：根据 RelNode 的类型返回其可匹配的 RelOptRuleOperand
   */
  private final Multimap<Class<? extends RelNode>, RelOptRuleOperand>
      classOperands = LinkedListMultimap.create();

  /**
   * List of all sets. Used only for debugging.
   */
  final List<RelSet> allSets = new ArrayList<>();

  /**
   * Canonical map from {@link String digest} to the unique
   * {@link RelNode relational expression} with that digest.
   * note：digest 与 relational expression 的对应关系
   *
   * <p>Row type is part of the key for the rare occasion that similar
   * expressions have different types, e.g. variants of
   * {@code Project(child=rel#1, a=null)} where a is a null INTEGER or a
   * null VARCHAR(10).
   */
  private final Map<String, RelNode> mapDigestToRel =
      new HashMap<>();

  /**
   * Map each registered expression ({@link RelNode}) to its equivalence set
   * ({@link RelSubset}).
   * note 每个注册的 RelNode，都有一个等价集合 RelSubset
   *
   * <p>We use an {@link IdentityHashMap} to simplify the process of merging
   * {@link RelSet} objects. Most {@link RelNode} objects are identified by
   * their digest, which involves the set that their child relational
   * expressions belong to. If those children belong to the same set, we have
   * to be careful, otherwise it gets incestuous.</p>
   */
  private final IdentityHashMap<RelNode, RelSubset> mapRel2Subset =
      new IdentityHashMap<>();

  /**
   * The importance of relational expressions.
   * note：每一个 relational expression 都有一个对应的 importance
   *
   * <p>The map contains only RelNodes whose importance has been overridden
   * using {@link RelOptPlanner#setImportance(RelNode, double)}. Other
   * RelNodes are presumed to have 'normal' importance.
   *
   * <p>If a RelNode has 0 importance, all {@link RelOptRuleCall}s using it
   * are ignored, and future RelOptRuleCalls are not queued up.
   */
  final Map<RelNode, Double> relImportances = new HashMap<>();

  /**
   * List of all schemas which have been registered.
   */
  private final Set<RelOptSchema> registeredSchemas = new HashSet<>();

  /**
   * Holds rule calls waiting to be fired.
   * note：等待被调用的 rule 集合
   */
  final RuleQueue ruleQueue = new RuleQueue(this);

  /**
   * Holds the currently registered RelTraitDefs.
   * note：RelTraitDefs 集合
   */
  private final List<RelTraitDef> traitDefs = new ArrayList<>();

  /**
   * Set of all registered rules.
   * note：所有注册的 rule
   */
  protected final Set<RelOptRule> ruleSet = new HashSet<>();

  //note: 一个递增的编号
  private int nextSetId = 0;

  /**
   * Incremented every time a relational expression is registered or two sets
   * are merged. Tells us whether anything is going on.
   * note：当有 relational expression 注册或 set merge 时，就加1
   */
  private int registerCount;

  /**
   * Listener for this planner, or null if none set.
   */
  RelOptListener listener;

  private RelNode originalRoot;

  /**
   * Whether the planner can accept new rules.
   */
  private boolean locked;

  private final List<RelOptMaterialization> materializations =
      new ArrayList<>();

  /**
   * Map of lattices by the qualified name of their star table.
   */
  private final Map<List<String>, RelOptLattice> latticeByName =
      new LinkedHashMap<>();

  final Map<RelNode, Provenance> provenanceMap = new HashMap<>();

  //note: 如果 rule 有调用时，放到这里，主要用于记录那些 RelNode 的来源
  final Deque<VolcanoRuleCall> ruleCallStack = new ArrayDeque<>();

  /** Zero cost, according to {@link #costFactory}. Not necessarily a
   * {@link org.apache.calcite.plan.volcano.VolcanoCost}. */
  private final RelOptCost zeroCost;

  /** Maps rule classes to their name, to ensure that the names are unique and
   * conform to rules. */
  private final SetMultimap<String, Class> ruleNames =
      LinkedHashMultimap.create();

  //~ Constructors -----------------------------------------------------------

  /**
   * Creates a uninitialized <code>VolcanoPlanner</code>. To fully initialize
   * it, the caller must register the desired set of relations, rules, and
   * calling conventions.
   * note: 创建一个没有初始化的 VolcanoPlanner，如果要进行初始化，调用者必须注册 set of relations、rules、calling conventions.
   */
  public VolcanoPlanner() {
    this(null, null);
  }

  /**
   * Creates a uninitialized <code>VolcanoPlanner</code>. To fully initialize
   * it, the caller must register the desired set of relations, rules, and
   * calling conventions.
   */
  public VolcanoPlanner(Context externalContext) {
    this(null, externalContext);
  }

  /**
   * Creates a {@code VolcanoPlanner} with a given cost factory.
   * note: 创建 VolcanoPlanner 实例，并制定 costFactory（默认为 VolcanoCost.FACTORY）
   */
  public VolcanoPlanner(RelOptCostFactory costFactory, //
      Context externalContext) {
    super(costFactory == null ? VolcanoCost.FACTORY : costFactory, //
        externalContext);
    this.zeroCost = this.costFactory.makeZeroCost();
  }

  //~ Methods ----------------------------------------------------------------

  protected VolcanoPlannerPhaseRuleMappingInitializer
      getPhaseRuleMappingInitializer() {
    return phaseRuleMap -> {
      // Disable all phases except OPTIMIZE by adding one useless rule name.
      //note: 通过添加一个无用的 rule name 来 disable 优化器的其他三个阶段
      phaseRuleMap.get(VolcanoPlannerPhase.PRE_PROCESS_MDR).add("xxx");
      phaseRuleMap.get(VolcanoPlannerPhase.PRE_PROCESS).add("xxx");
      phaseRuleMap.get(VolcanoPlannerPhase.CLEANUP).add("xxx");
    };
  }

  // implement RelOptPlanner
  public boolean isRegistered(RelNode rel) {
    return mapRel2Subset.get(rel) != null;
  }

  public void setRoot(RelNode rel) {
    // We're registered all the rules, and therefore RelNode classes,
    // we're interested in, and have not yet started calling metadata providers.
    // So now is a good time to tell the metadata layer what to expect.
    registerMetadataRels();

    //note: 注册相应的 RelNode，会做一系列的初始化操作, RelNode 会有对应的 RelSubset
    this.root = registerImpl(rel, null);
    if (this.originalRoot == null) {
      this.originalRoot = rel;
    }

    // Making a node the root changes its importance.
    //note: 计算 root subset 的 importance
    this.ruleQueue.recompute(this.root);
    ensureRootConverters();
  }

  public RelNode getRoot() {
    return root;
  }

  @Override public List<RelOptMaterialization> getMaterializations() {
    return ImmutableList.copyOf(materializations);
  }

  @Override public void addMaterialization(
      RelOptMaterialization materialization) {
    materializations.add(materialization);
  }

  @Override public void addLattice(RelOptLattice lattice) {
    latticeByName.put(lattice.starRelOptTable.getQualifiedName(), lattice);
  }

  @Override public RelOptLattice getLattice(RelOptTable table) {
    return latticeByName.get(table.getQualifiedName());
  }

  private void registerMaterializations() {
    // Avoid using materializations while populating materializations!
    //note: 初始化时，如果没有指定 Context 参数，这里就会返回 null
    final CalciteConnectionConfig config =
        context.unwrap(CalciteConnectionConfig.class);
    if (config == null || !config.materializationsEnabled()) {
      return;
    }

    // Register rels using materialized views.
    final List<Pair<RelNode, List<RelOptMaterialization>>> materializationUses =
        RelOptMaterializations.useMaterializedViews(originalRoot, materializations);
    for (Pair<RelNode, List<RelOptMaterialization>> use : materializationUses) {
      RelNode rel = use.left;
      Hook.SUB.run(rel);
      registerImpl(rel, root.set);
    }

    // Register table rels of materialized views that cannot find a substitution
    // in root rel transformation but can potentially be useful.
    final Set<RelOptMaterialization> applicableMaterializations =
        new HashSet<>(
            RelOptMaterializations.getApplicableMaterializations(
                originalRoot, materializations));
    for (Pair<RelNode, List<RelOptMaterialization>> use : materializationUses) {
      applicableMaterializations.removeAll(use.right);
    }
    for (RelOptMaterialization materialization : applicableMaterializations) {
      RelSubset subset = registerImpl(materialization.queryRel, null);
      RelNode tableRel2 =
          RelOptUtil.createCastRel(
              materialization.tableRel,
              materialization.queryRel.getRowType(),
              true);
      registerImpl(tableRel2, subset.set);
    }

    // Register rels using lattices.
    final List<Pair<RelNode, RelOptLattice>> latticeUses =
        RelOptMaterializations.useLattices(
            originalRoot, ImmutableList.copyOf(latticeByName.values()));
    if (!latticeUses.isEmpty()) {
      RelNode rel = latticeUses.get(0).left;
      Hook.SUB.run(rel);
      registerImpl(rel, root.set);
    }
  }

  /**
   * Finds an expression's equivalence set. If the expression is not
   * registered, returns null.
   *
   * note: 查找 RelNode 的等价集
   * @param rel Relational expression
   * @return Equivalence set that expression belongs to, or null if it is not
   * registered
   */
  public RelSet getSet(RelNode rel) {
    assert rel != null : "pre: rel != null";
    final RelSubset subset = getSubset(rel);
    if (subset != null) {
      assert subset.set != null;
      return subset.set;
    }
    return null;
  }

  //note: 添加 RelTraitDef
  @Override public boolean addRelTraitDef(RelTraitDef relTraitDef) {
    return !traitDefs.contains(relTraitDef) && traitDefs.add(relTraitDef);
  }

  //note：清空所有的 RelTrait
  @Override public void clearRelTraitDefs() {
    traitDefs.clear();
  }

  @Override public List<RelTraitDef> getRelTraitDefs() {
    return traitDefs;
  }

  //note: 新建一个 traitSet，并将traitDefs原有的 trait 添加进去返回
  @Override public RelTraitSet emptyTraitSet() {
    RelTraitSet traitSet = super.emptyTraitSet();
    for (RelTraitDef traitDef : traitDefs) {
      if (traitDef.multiple()) {
        // TODO: restructure RelTraitSet to allow a list of entries
        //  for any given trait
      }
      traitSet = traitSet.plus(traitDef.getDefault()); //note:
    }
    return traitSet;
  }

  @Override public void clear() {
    super.clear();
    for (RelOptRule rule : ImmutableList.copyOf(ruleSet)) {
      removeRule(rule);
    }
    this.classOperands.clear();
    this.allSets.clear();
    this.mapDigestToRel.clear();
    this.mapRel2Subset.clear();
    this.relImportances.clear();
    this.ruleQueue.clear();
    this.ruleNames.clear();
    this.materializations.clear();
    this.latticeByName.clear();
  }

  public List<RelOptRule> getRules() {
    return ImmutableList.copyOf(ruleSet);
  }

  //note: 添加 rule
  public boolean addRule(RelOptRule rule) {
    if (locked) {
      return false;
    }
    if (ruleSet.contains(rule)) {
      // Rule already exists.
      return false;
    }
    final boolean added = ruleSet.add(rule);
    assert added;

    final String ruleName = rule.toString();
    //note: 这里的 ruleNames 允许重复的 key 值，但是这里还是要求 rule description 保持唯一的，与 rule 一一对应
    if (ruleNames.put(ruleName, rule.getClass())) {
      Set<Class> x = ruleNames.get(ruleName);
      if (x.size() > 1) {
        throw new RuntimeException("Rule description '" + ruleName
            + "' is not unique; classes: " + x);
      }
    }

    //note: 注册一个 rule 的 description（保存在 mapDescToRule 中）
    mapRuleDescription(rule);

    // Each of this rule's operands is an 'entry point' for a rule call.
    // Register each operand against all concrete sub-classes that could match
    // it.
    //note: 记录每个 sub-classes 与 operand 的关系（如果能 match 的话，就记录一次）
    //note: 一个 RelOptRuleOperand 只会有一个 class 与之对应，这里找的是 subclass
    for (RelOptRuleOperand operand : rule.getOperands()) {
      for (Class<? extends RelNode> subClass
          : subClasses(operand.getMatchedClass())) {
        classOperands.put(subClass, operand);
      }
    }

    // If this is a converter rule, check that it operates on one of the
    // kinds of trait we are interested in, and if so, register the rule
    // with the trait.
    //note: 对于 ConverterRule 的操作，如果其 ruleTraitDef 类型包含在我们初始化的 traitDefs 中，
    //note: 就注册这个 converterRule 到 ruleTraitDef 中
    //note: 如果不包含 ruleTraitDef，这个 ConverterRule 在本次优化的过程中是用不到的
    if (rule instanceof ConverterRule) {
      ConverterRule converterRule = (ConverterRule) rule;

      final RelTrait ruleTrait = converterRule.getInTrait();
      final RelTraitDef ruleTraitDef = ruleTrait.getTraitDef();
      if (traitDefs.contains(ruleTraitDef)) { //note: 这里注册好像也没有用到
        ruleTraitDef.registerConverterRule(this, converterRule);
      }
    }

    return true;
  }

  public boolean removeRule(RelOptRule rule) {
    if (!ruleSet.remove(rule)) {
      // Rule was not present.
      return false;
    }

    // Remove description.
    unmapRuleDescription(rule);

    // Remove operands.
    classOperands.values().removeIf(entry -> entry.getRule().equals(rule));

    // Remove trait mappings. (In particular, entries from conversion
    // graph.)
    if (rule instanceof ConverterRule) {
      ConverterRule converterRule = (ConverterRule) rule;
      final RelTrait ruleTrait = converterRule.getInTrait();
      final RelTraitDef ruleTraitDef = ruleTrait.getTraitDef();
      if (traitDefs.contains(ruleTraitDef)) {
        ruleTraitDef.deregisterConverterRule(this, converterRule);
      }
    }
    return true;
  }

  //note: 注册 RelNode 的 class，如果这个 class 满足 rule 的条件，就注册到 classOperands 中
  @Override protected void onNewClass(RelNode node) {
    super.onNewClass(node);

    // Create mappings so that instances of this class will match existing
    // operands.
    final Class<? extends RelNode> clazz = node.getClass();
    for (RelOptRule rule : ruleSet) {
      for (RelOptRuleOperand operand : rule.getOperands()) {
        if (operand.getMatchedClass().isAssignableFrom(clazz)) {
          classOperands.put(clazz, operand);
        }
      }
    }
  }

  //note: Changes a relational expression to an equivalent one with a different set of traits.
  public RelNode changeTraits(final RelNode rel, RelTraitSet toTraits) {
    assert !rel.getTraitSet().equals(toTraits);
    assert toTraits.allSimple();

    //note: 注册这个 RelNode
    RelSubset rel2 = ensureRegistered(rel, null);
    //note: 如果 RelTraitSet 刚好匹配
    if (rel2.getTraitSet().equals(toTraits)) {
      return rel2;
    }

    //note: 如果 RelTraitSet 不匹配，那么就在 RelSet 中新建一个 RelSubset
    return rel2.set.getOrCreateSubset(rel.getCluster(), toTraits.simplify());
  }

  public RelOptPlanner chooseDelegate() {
    return this;
  }

  /**
   * Finds the most efficient expression to implement the query given via
   * {@link org.apache.calcite.plan.RelOptPlanner#setRoot(org.apache.calcite.rel.RelNode)}.
   *
   * note：找到最有效率的 relational expression，这个算法包含一系列阶段，每个阶段被触发的 rules 可能不同
   * <p>The algorithm executes repeatedly in a series of phases. In each phase
   * the exact rules that may be fired varies. The mapping of phases to rule
   * sets is maintained in the {@link #ruleQueue}.
   *
   * note：在每个阶段，planner 都会初始化这个 RelSubset 的 importance，planner 会遍历 rule queue 中 rules 直到：
   * note：1. rule queue 变为空；
   * note：2. 对于 ambitious planner，最近 cost 不再提高时（具体来说，第一次找到一个可执行计划时，需要达到需要迭代总数的10%或更大）；
   * note：3. 对于 non-ambitious planner，当找到一个可执行的计划就行；
   * <p>In each phase, the planner sets the initial importance of the existing
   * RelSubSets ({@link #setInitialImportance()}). The planner then iterates
   * over the rule matches presented by the rule queue until:
   *
   * <ol>
   * <li>The rule queue becomes empty.</li>
   * <li>For ambitious planners: No improvements to the plan have been made
   * recently (specifically within a number of iterations that is 10% of the
   * number of iterations necessary to first reach an implementable plan or 25
   * iterations whichever is larger).</li>
   * <li>For non-ambitious planners: When an implementable plan is found.</li>
   * </ol>
   *
   * note：此外，如果每10次迭代之后，没有一个可实现的计划，包含 logical RelNode 的 RelSubSets 将会通过 injectImportanceBoost 给一个 importance；
   * <p>Furthermore, after every 10 iterations without an implementable plan,
   * RelSubSets that contain only logical RelNodes are given an importance
   * boost via {@link #injectImportanceBoost()}. Once an implementable plan is
   * found, the artificially raised importance values are cleared (see
   * {@link #clearImportanceBoost()}).
   *
   * @return the most efficient RelNode tree found for implementing the given
   * query
   */
  public RelNode findBestExp() {
    //note: 确保 root relational expression 的 subset（RelSubset）在它的等价集（RelSet）中包含所有 RelSubset 的 converter
    //note: 来保证 planner 从其他的 subsets 找到的实现方案可以转换为 root，否则可能因为 convention 不同，无法实施
    ensureRootConverters();
    //note: materialized views 相关，这里可以先忽略~
    registerMaterializations();
    int cumulativeTicks = 0; //note: 四个阶段通用的变量
    //note: 不同的阶段，总共四个阶段，实际上只有 OPTIMIZE 这个阶段有效，因为其他阶段不会有 RuleMatch
    for (VolcanoPlannerPhase phase : VolcanoPlannerPhase.values()) {
      //note: 在不同的阶段，初始化 RelSubSets 相应的 importance
      //note: root 节点往下子节点的 importance 都会被初始化
      setInitialImportance();

      //note: 默认是 VolcanoCost
      RelOptCost targetCost = costFactory.makeHugeCost();
      int tick = 0;
      int firstFiniteTick = -1;
      int splitCount = 0;
      int giveUpTick = Integer.MAX_VALUE;

      while (true) {
        ++tick;
        ++cumulativeTicks;
        //note: 第一次运行是 false，两个不是一个对象，一个是 costFactory.makeHugeCost， 一个是 costFactory.makeInfiniteCost
        //note: 如果低于目标 cost，这里再重新设置一个新目标、新的 giveUpTick
        if (root.bestCost.isLe(targetCost)) {
          //note: 本阶段第一次运行，目的是为了调用 clearImportanceBoost 方法，清除相应的 importance 信息
          if (firstFiniteTick < 0) {
            firstFiniteTick = cumulativeTicks;

            //note: 对于那些手动提高 importance 的 RelSubset 进行重新计算
            clearImportanceBoost();
          }
          if (ambitious) {
            // Choose a slightly more ambitious target cost, and
            // try again. If it took us 1000 iterations to find our
            // first finite plan, give ourselves another 100
            // iterations to reduce the cost by 10%.
            //note: 设置 target 为当前 best cost 的 0.9，调整相应的目标，再进行优化
            targetCost = root.bestCost.multiplyBy(0.9);
            ++splitCount;
            if (impatient) {
              if (firstFiniteTick < 10) {
                // It's possible pre-processing can create
                // an implementable plan -- give us some time
                // to actually optimize it.
                //note: 有可能在 pre-processing 阶段就实现一个 implementable plan，所以先设置一个值，后面再去优化
                giveUpTick = cumulativeTicks + 25;
              } else {
                giveUpTick =
                    cumulativeTicks
                        + Math.max(firstFiniteTick / 10, 25);
              }
            }
          } else {
            break;
          }
        //note: 最近没有任何进步（超过 giveUpTick 限制，还没达到目标值），直接采用当前的 best plan
        } else if (cumulativeTicks > giveUpTick) {
          // We haven't made progress recently. Take the current best.
          break;
        } else if (root.bestCost.isInfinite() && ((tick % 10) == 0)) {
          injectImportanceBoost();
        }

        LOGGER.debug("PLANNER = {}; TICK = {}/{}; PHASE = {}; COST = {}",
            this, cumulativeTicks, tick, phase.toString(), root.bestCost);

        VolcanoRuleMatch match = ruleQueue.popMatch(phase);
        //note: 如果没有规则，会直接退出当前的阶段
        if (match == null) {
          break;
        }

        assert match.getRule().matches(match);
        //note: 做相应的规则匹配
        match.onMatch();

        // The root may have been merged with another
        // subset. Find the new root subset.
        root = canonize(root);
      }

      //note: 当期阶段完成，移除 ruleQueue 中记录的 rule-match list
      ruleQueue.phaseCompleted(phase);
    }
    if (LOGGER.isTraceEnabled()) {
      StringWriter sw = new StringWriter();
      final PrintWriter pw = new PrintWriter(sw);
      dump(pw);
      pw.flush();
      LOGGER.trace(sw.toString());
    }
    //note: 根据 plan 构建其 RelNode 树
    RelNode cheapest = root.buildCheapestPlan(this);
    if (LOGGER.isDebugEnabled()) {
      LOGGER.debug(
          "Cheapest plan:\n{}", RelOptUtil.toString(cheapest, SqlExplainLevel.ALL_ATTRIBUTES));

      LOGGER.debug("Provenance:\n{}", provenance(cheapest));
    }
    return cheapest;
  }

  /** Informs {@link JaninoRelMetadataProvider} about the different kinds of
   * {@link RelNode} that we will be dealing with. It will reduce the number
   * of times that we need to re-generate the provider. */
  private void registerMetadataRels() {
    JaninoRelMetadataProvider.DEFAULT.register(classOperands.keySet());
  }

  /** Ensures that the subset that is the root relational expression contains
   * converters to all other subsets in its equivalence set.
   *
   * note：确保 root relational expression 的 subset 在它的等价集合中包含所有subset 的 converter
   * <p>Thus the planner tries to find cheap implementations of those other
   * subsets, which can then be converted to the root. This is the only place
   * in the plan where explicit converters are required; elsewhere, a consumer
   * will be asking for the result in a particular convention, but the root has
   * no consumers. */
  void ensureRootConverters() {
    final Set<RelSubset> subsets = new HashSet<>();
    for (RelNode rel : root.getRels()) {
      if (rel instanceof AbstractConverter) {
        subsets.add((RelSubset) ((AbstractConverter) rel).getInput());
      }
    }
    for (RelSubset subset : root.set.subsets) { //note: RelSubset 是具有同样 trait 属性的等价集合
      final ImmutableList<RelTrait> difference =
          root.getTraitSet().difference(subset.getTraitSet());
      if (difference.size() == 1 && subsets.add(subset)) {
        register(
            new AbstractConverter(subset.getCluster(), subset,
                difference.get(0).getTraitDef(), root.getTraitSet()),
            root);
      }
    }
  }

  /**
   * Returns a multi-line string describing the provenance of a tree of
   * relational expressions. For each node in the tree, prints the rule that
   * created the node, if any. Recursively describes the provenance of the
   * relational expressions that are the arguments to that rule.
   *
   * <p>Thus, every relational expression and rule invocation that affected
   * the final outcome is described in the provenance. This can be useful
   * when finding the root cause of "mistakes" in a query plan.</p>
   *
   * @param root Root relational expression in a tree
   * @return Multi-line string describing the rules that created the tree
   */
  //note: 只有在 debug 的情况下，才打印
  private String provenance(RelNode root) {
    final StringWriter sw = new StringWriter();
    final PrintWriter pw = new PrintWriter(sw);
    final List<RelNode> nodes = new ArrayList<>();
    new RelVisitor() {
      public void visit(RelNode node, int ordinal, RelNode parent) {
        nodes.add(node);
        super.visit(node, ordinal, parent);
      }
      // CHECKSTYLE: IGNORE 1
    }.go(root);
    final Set<RelNode> visited = new HashSet<>();
    for (RelNode node : nodes) {
      provenanceRecurse(pw, node, 0, visited);
    }
    pw.flush();
    return sw.toString();
  }

  /**
   * Helper for {@link #provenance(org.apache.calcite.rel.RelNode)}.
   */
  private void provenanceRecurse(
      PrintWriter pw, RelNode node, int i, Set<RelNode> visited) {
    Spaces.append(pw, i * 2);
    if (!visited.add(node)) {
      pw.println("rel#" + node.getId() + " (see above)");
      return;
    }
    pw.println(node);
    final Provenance o = provenanceMap.get(node);
    Spaces.append(pw, i * 2 + 2);
    if (o == Provenance.EMPTY) {
      pw.println("no parent");
    } else if (o instanceof DirectProvenance) {
      RelNode rel = ((DirectProvenance) o).source;
      pw.println("direct");
      provenanceRecurse(pw, rel, i + 2, visited);
    } else if (o instanceof RuleProvenance) {
      RuleProvenance rule = (RuleProvenance) o;
      pw.println("call#" + rule.callId + " rule [" + rule.rule + "]");
      for (RelNode rel : rule.rels) {
        provenanceRecurse(pw, rel, i + 2, visited);
      }
    } else if (o == null && node instanceof RelSubset) {
      // A few operands recognize subsets, not individual rels.
      // The first rel in the subset is deemed to have created it.
      final RelSubset subset = (RelSubset) node;
      pw.println("subset " + subset);
      provenanceRecurse(pw, subset.getRelList().get(0), i + 2, visited);
    } else {
      throw new AssertionError("bad type " + o);
    }
  }

  //note: 设置初始的 importance
  private void setInitialImportance() {
    RelVisitor visitor =
        new RelVisitor() {
          int depth = 0;
          final Set<RelSubset> visitedSubsets = new HashSet<>();

          //note: Visits a node during a traversal.
          public void visit(
              RelNode p,
              int ordinal,
              RelNode parent) {
            if (p instanceof RelSubset) {
              RelSubset subset = (RelSubset) p;

              if (visitedSubsets.contains(subset)) {
                return;
              }

              if (subset != root) { //note: 计算 importance，并更新到缓存中
                Double importance = Math.pow(0.9, (double) depth);

                ruleQueue.updateImportance(subset, importance);
              }

              visitedSubsets.add(subset); //note: 计算过 importance 的 RelNode 记录下来

              depth++;
              for (RelNode rel : subset.getRels()) { //note: RelSubset 中 rels 都会初始化一下
                visit(rel, -1, subset);
              }
              depth--;
            } else {
              super.visit(p, ordinal, parent);
            }
          }
        };

    visitor.go(root);
  }

  /**
   * Finds RelSubsets in the plan that contain only rels of
   * {@link Convention#NONE} and boosts their importance by 25%.
   * note：将 RelSubsets 的 importance 增加25%，如果 RelSubsets 的 RelNode 的 Convention 是 none 的话
   */
  private void injectImportanceBoost() {
    final Set<RelSubset> requireBoost = new HashSet<>();

  SUBSET_LOOP:
    for (RelSubset subset : ruleQueue.subsetImportances.keySet()) {
      for (RelNode rel : subset.getRels()) {
        if (rel.getConvention() != Convention.NONE) {
          continue SUBSET_LOOP;
        }
      }

      requireBoost.add(subset);
    }

    ruleQueue.boostImportance(requireBoost, 1.25);
  }

  /**
   * Clear all importance boosts.
   * note：清除所有增加的 importance（这里是空集合，并没有清除）
   */
  private void clearImportanceBoost() {
    Collection<RelSubset> empty = Collections.emptySet();

    ruleQueue.boostImportance(empty, 1.0);
  }

  //note: 注册一个 RelNode
  public RelSubset register(
      RelNode rel,
      RelNode equivRel) {
    assert !isRegistered(rel) : "pre: isRegistered(rel)";
    final RelSet set;
    if (equivRel == null) { //note: equivRel 为 null 时，设置其 RelSet 为 null，并注册
      set = null;
    } else {
      assert RelOptUtil.equal(
          "rel rowtype",
          rel.getRowType(),
          "equivRel rowtype",
          equivRel.getRowType(),
          Litmus.THROW);
      set = getSet(equivRel);
    }
    //note: 最开始初始化时，这里会循环调用（RelNode 的 input），将 RelNode 全部注册（注册的意思，其实就是做相应的转换和初始化操作）
    final RelSubset subset = registerImpl(rel, set);

    // Checking if tree is valid considerably slows down planning
    // Only doing it if logger level is debug or finer
    if (LOGGER.isDebugEnabled()) {
      assert isValid(Litmus.THROW);
    }

    return subset;
  }

  //note: 注册 RelNode
  public RelSubset ensureRegistered(RelNode rel, RelNode equivRel) {
    final RelSubset subset = getSubset(rel);
    if (subset != null) { //note: 如果该 RelNode 对应的
      if (equivRel != null) {
        final RelSubset equivSubset = getSubset(equivRel);
        if (subset.set != equivSubset.set) {
          merge(equivSubset.set, subset.set);
        }
      }
      return subset;
    } else { //note: 还没有注册的情况下，进行注册，实际上就是初始化到
      return register(rel, equivRel);
    }
  }

  /**
   * Checks internal consistency.
   */
  protected boolean isValid(Litmus litmus) {
    for (RelSet set : allSets) {
      if (set.equivalentSet != null) {
        return litmus.fail("set [{}] has been merged: it should not be in the list", set);
      }
      for (RelSubset subset : set.subsets) {
        if (subset.set != set) {
          return litmus.fail("subset [{}] is in wrong set [{}]",
              subset.getDescription(), set);
        }
        for (RelNode rel : subset.getRels()) {
          RelOptCost relCost = getCost(rel, rel.getCluster().getMetadataQuery());
          if (relCost.isLt(subset.bestCost)) {
            return litmus.fail("rel [{}] has lower cost {} than best cost {} of subset [{}]",
                rel.getDescription(), relCost, subset.bestCost, subset.getDescription());
          }
        }
      }
    }
    return litmus.succeed();
  }

  public void registerAbstractRelationalRules() {
    addRule(FilterJoinRule.FILTER_ON_JOIN);
    addRule(FilterJoinRule.JOIN);
    addRule(AbstractConverter.ExpandConversionRule.INSTANCE);
    addRule(JoinCommuteRule.INSTANCE);
    addRule(SemiJoinRule.PROJECT);
    addRule(SemiJoinRule.JOIN);
    if (CalcitePrepareImpl.COMMUTE) {
      addRule(JoinAssociateRule.INSTANCE);
    }
    addRule(AggregateRemoveRule.INSTANCE);
    addRule(UnionToDistinctRule.INSTANCE);
    addRule(ProjectRemoveRule.INSTANCE);
    addRule(AggregateJoinTransposeRule.INSTANCE);
    addRule(AggregateProjectMergeRule.INSTANCE);
    addRule(CalcRemoveRule.INSTANCE);
    addRule(SortRemoveRule.INSTANCE);

    // todo: rule which makes Project({OrdinalRef}) disappear
  }

  public void registerSchema(RelOptSchema schema) {
    if (registeredSchemas.add(schema)) {
      try {
        schema.registerRules(this);
      } catch (Exception e) {
        throw new AssertionError("While registering schema " + schema, e);
      }
    }
  }

  //note: Computes the cost of a RelNode.
  public RelOptCost getCost(RelNode rel, RelMetadataQuery mq) {
    assert rel != null : "pre-condition: rel != null";
    if (rel instanceof RelSubset) { //note: 如果是 RelSubset，证明是已经计算 cost 的 subset
      return ((RelSubset) rel).bestCost;
    }
    if (rel.getTraitSet().getTrait(ConventionTraitDef.INSTANCE)
        == Convention.NONE) {
      return costFactory.makeInfiniteCost(); //note: 这种情况下也会返回 infinite Cost
    }
    //note: 计算其 cost
    RelOptCost cost = mq.getNonCumulativeCost(rel);
    if (!zeroCost.isLt(cost)) { //note: cost 比0还小的情况
      // cost must be positive, so nudge it
      cost = costFactory.makeTinyCost();
    }
    //note: RelNode 的 cost 会把其 input 全部加上
    for (RelNode input : rel.getInputs()) {
      cost = cost.plus(getCost(input, mq));
    }
    return cost;
  }

  /**
   * Returns the subset that a relational expression belongs to.
   *
   * @param rel Relational expression
   * @return Subset it belongs to, or null if it is not registered
   */
  public RelSubset getSubset(RelNode rel) {
    assert rel != null : "pre: rel != null";
    if (rel instanceof RelSubset) {
      return (RelSubset) rel;
    } else {
      return mapRel2Subset.get(rel);
    }
  }

  public RelSubset getSubset(
      RelNode rel,
      RelTraitSet traits) {
    return getSubset(rel, traits, false);
  }

  public RelSubset getSubset(
      RelNode rel,
      RelTraitSet traits,
      boolean createIfMissing) {
    if ((rel instanceof RelSubset) && (rel.getTraitSet().equals(traits))) {
      return (RelSubset) rel;
    }
    RelSet set = getSet(rel);
    if (set == null) {
      return null;
    }
    if (createIfMissing) {
      return set.getOrCreateSubset(rel.getCluster(), traits);
    }
    return set.getSubset(traits);
  }

  private RelNode changeTraitsUsingConverters(
      RelNode rel,
      RelTraitSet toTraits,
      boolean allowAbstractConverters) {
    final RelTraitSet fromTraits = rel.getTraitSet();

    assert fromTraits.size() >= toTraits.size();

    final boolean allowInfiniteCostConverters =
        SaffronProperties.INSTANCE.allowInfiniteCostConverters().get();

    // Traits may build on top of another...for example a collation trait
    // would typically come after a distribution trait since distribution
    // destroys collation; so when doing the conversion below we use
    // fromTraits as the trait of the just previously converted RelNode.
    // Also, toTraits may have fewer traits than fromTraits, excess traits
    // will be left as is.  Finally, any null entries in toTraits are
    // ignored.
    RelNode converted = rel;
    for (int i = 0; (converted != null) && (i < toTraits.size()); i++) {
      RelTrait fromTrait = converted.getTraitSet().getTrait(i);
      final RelTraitDef traitDef = fromTrait.getTraitDef();
      RelTrait toTrait = toTraits.getTrait(i);

      if (toTrait == null) {
        continue;
      }

      assert traitDef == toTrait.getTraitDef();
//            if (fromTrait.subsumes(toTrait)) {
      if (fromTrait.equals(toTrait)) {
        // No need to convert; it's already correct.
        continue;
      }

      rel =
          traitDef.convert(
              this,
              converted,
              toTrait,
              allowInfiniteCostConverters);
      if (rel != null) {
        assert rel.getTraitSet().getTrait(traitDef).satisfies(toTrait);
        rel =
            completeConversion(
                rel, allowInfiniteCostConverters, toTraits,
                Expressions.list(traitDef));
        if (rel != null) {
          register(rel, converted);
        }
      }

      if ((rel == null) && allowAbstractConverters) {
        RelTraitSet stepTraits =
            converted.getTraitSet().replace(toTrait);

        rel = getSubset(converted, stepTraits);
      }

      converted = rel;
    }

    // make sure final converted traitset subsumes what was required
    if (converted != null) {
      assert converted.getTraitSet().satisfies(toTraits);
    }

    return converted;
  }

  /**
   * Converts traits using well-founded induction. We don't require that
   * each conversion preserves all traits that have previously been converted,
   * but if it changes "locked in" traits we'll try some other conversion.
   *
   * @param rel                         Relational expression
   * @param allowInfiniteCostConverters Whether to allow infinite converters
   * @param toTraits                    Target trait set
   * @param usedTraits                  Traits that have been locked in
   * @return Converted relational expression
   */
  private RelNode completeConversion(
      RelNode rel,
      boolean allowInfiniteCostConverters,
      RelTraitSet toTraits,
      Expressions.FluentList<RelTraitDef> usedTraits) {
    if (true) {
      return rel;
    }
    for (RelTrait trait : rel.getTraitSet()) {
      if (toTraits.contains(trait)) {
        // We're already a match on this trait type.
        continue;
      }
      final RelTraitDef traitDef = trait.getTraitDef();
      RelNode rel2 =
          traitDef.convert(
              this,
              rel,
              toTraits.getTrait(traitDef),
              allowInfiniteCostConverters);

      // if any of the used traits have been knocked out, we could be
      // heading for a cycle.
      for (RelTraitDef usedTrait : usedTraits) {
        if (!rel2.getTraitSet().contains(usedTrait)) {
          continue;
        }
      }
      // recursive call, to convert one more trait
      rel =
          completeConversion(
              rel2,
              allowInfiniteCostConverters,
              toTraits,
              usedTraits.append(traitDef));
      if (rel != null) {
        return rel;
      }
    }
    assert rel.getTraitSet().equals(toTraits);
    return rel;
  }

  RelNode changeTraitsUsingConverters(
      RelNode rel,
      RelTraitSet toTraits) {
    return changeTraitsUsingConverters(rel, toTraits, false);
  }

  //note: 检查是否满足 converter
  void checkForSatisfiedConverters(
      RelSet set,
      RelNode rel) {
    int i = 0;
    while (i < set.abstractConverters.size()) {
      AbstractConverter converter = set.abstractConverters.get(i);
      RelNode converted =
          changeTraitsUsingConverters(
              rel,
              converter.getTraitSet());
      if (converted == null) {
        i++; // couldn't convert this; move on to the next
      } else {
        if (!isRegistered(converted)) {
          registerImpl(converted, set);
        }
        set.abstractConverters.remove(converter); // success
      }
    }
  }

  public void setImportance(RelNode rel, double importance) {
    assert rel != null;
    if (importance == 0d) {
      relImportances.put(rel, importance);
    }
  }

  /**
   * Dumps the internal state of this VolcanoPlanner to a writer.
   * note: 输出当前 planner 的状态
   *
   * @param pw Print writer
   * @see #normalizePlan(String)
   */
  public void dump(PrintWriter pw) {
    pw.println("Root: " + root.getDescription());
    pw.println("Original rel:");

    if (originalRoot != null) {
      originalRoot.explain(
          new RelWriterImpl(pw, SqlExplainLevel.ALL_ATTRIBUTES, false));
    }
    if (DUMP_SETS) {
      pw.println();
      pw.println("Sets:");
      dumpSets(pw);
    }
    if (DUMP_GRAPHVIZ) {
      pw.println();
      pw.println("Graphviz:");
      dumpGraphviz(pw);
    }
  }

  public String toDot() {
    StringWriter sw = new StringWriter();
    PrintWriter pw = new PrintWriter(sw);
    dumpGraphviz(pw);
    pw.flush();
    return sw.toString();
  }

  //note: 看下 subset 的输出
  private void dumpSets(PrintWriter pw) {
    Ordering<RelSet> ordering = Ordering.from(Comparator.comparingInt(o -> o.id));
    for (RelSet set : ordering.immutableSortedCopy(allSets)) {
      pw.println("Set#" + set.id
          + ", type: " + set.subsets.get(0).getRowType());
      int j = -1;
      for (RelSubset subset : set.subsets) {
        ++j;
        pw.println(
            "\t" + subset.getDescription() + ", best="
            + ((subset.best == null) ? "null"
                : ("rel#" + subset.best.getId())) + ", importance="
                + ruleQueue.getImportance(subset));
        assert subset.set == set;
        for (int k = 0; k < j; k++) {
          assert !set.subsets.get(k).getTraitSet().equals(
              subset.getTraitSet());
        }
        for (RelNode rel : subset.getRels()) {
          // "\t\trel#34:JavaProject(rel#32:JavaFilter(...), ...)"
          pw.print("\t\t" + rel.getDescription());
          for (RelNode input : rel.getInputs()) {
            RelSubset inputSubset =
                getSubset(
                    input,
                    input.getTraitSet());
            RelSet inputSet = inputSubset.set;
            if (input instanceof RelSubset) {
              final Iterator<RelNode> rels =
                  inputSubset.getRels().iterator();
              if (rels.hasNext()) {
                input = rels.next();
                assert input.getTraitSet().satisfies(inputSubset.getTraitSet());
                assert inputSet.rels.contains(input);
                assert inputSet.subsets.contains(inputSubset);
              }
            }
          }
          Double importance = relImportances.get(rel);
          if (importance != null) {
            pw.print(", importance=" + importance);
          }
          RelMetadataQuery mq = rel.getCluster().getMetadataQuery();
          pw.print(", rowcount=" + mq.getRowCount(rel));
          pw.println(", cumulative cost=" + getCost(rel, mq));
        }
      }
    }
  }

  //note: Graphviz 的输出
  private void dumpGraphviz(PrintWriter pw) {
    Ordering<RelSet> ordering = Ordering.from(Comparator.comparingInt(o -> o.id));
    Set<RelNode> activeRels = new HashSet<>();
    for (VolcanoRuleCall volcanoRuleCall : ruleCallStack) {
      activeRels.addAll(Arrays.asList(volcanoRuleCall.rels));
    }
    pw.println("digraph G {");
    pw.println("\troot [style=filled,label=\"Root\"];");
    PartiallyOrderedSet<RelSubset> subsetPoset = new PartiallyOrderedSet<>(
        (e1, e2) -> e1.getTraitSet().satisfies(e2.getTraitSet()));
    Set<RelSubset> nonEmptySubsets = new HashSet<>();
    for (RelSet set : ordering.immutableSortedCopy(allSets)) {
      pw.print("\tsubgraph cluster");
      pw.print(set.id);
      pw.println("{");
      pw.print("\t\tlabel=");
      Util.printJavaString(pw, "Set " + set.id + " " + set.subsets.get(0).getRowType(), false);
      pw.print(";\n");
      for (RelNode rel : set.rels) {
        String traits = "." + rel.getTraitSet().toString();
        pw.print("\t\trel");
        pw.print(rel.getId());
        pw.print(" [label=");
        RelMetadataQuery mq = rel.getCluster().getMetadataQuery();
        Util.printJavaString(pw,
            rel.getDescription().replace(traits, "")
                + "\nrows=" + mq.getRowCount(rel) + ", cost=" + getCost(rel, mq), false);
        RelSubset relSubset = getSubset(rel);
        if (!(rel instanceof AbstractConverter)) {
          nonEmptySubsets.add(relSubset);
        }
        if (relSubset.best == rel) {
          pw.print(",color=blue");
        }
        if (activeRels.contains(rel)) {
          pw.print(",style=dashed");
        }
        pw.print(",shape=box");
        pw.println("]");
      }

      subsetPoset.clear();
      for (RelSubset subset : set.subsets) {
        subsetPoset.add(subset);
        pw.print("\t\tsubset");
        pw.print(subset.getId());
        pw.print(" [label=");
        Util.printJavaString(pw, subset.getDescription(), false);
        boolean empty = !nonEmptySubsets.contains(subset);
        if (empty) {
          // We don't want to iterate over rels when we know the set is not empty
          for (RelNode rel : subset.getRels()) {
            if (!(rel instanceof AbstractConverter)) {
              empty = false;
              break;
            }
          }
          if (empty) {
            pw.print(",color=red");
          }
        }
        if (activeRels.contains(subset)) {
          pw.print(",style=dashed");
        }
        pw.print("]\n");
      }

      for (RelSubset subset : subsetPoset) {
        for (RelSubset parent : subsetPoset.getChildren(subset)) {
          pw.print("\t\tsubset");
          pw.print(subset.getId());
          pw.print(" -> subset");
          pw.print(parent.getId());
          pw.print(";");
        }
      }

      pw.print("\t}\n");
    }
    // Note: it is important that all the links are declared AFTER declaration of the nodes
    // Otherwise Graphviz creates nodes implicitly, and puts them into a wrong cluster
    pw.print("\troot -> subset");
    pw.print(root.getId());
    pw.println(";");
    for (RelSet set : ordering.immutableSortedCopy(allSets)) {
      for (RelNode rel : set.rels) {
        RelSubset relSubset = getSubset(rel);
        pw.print("\tsubset");
        pw.print(relSubset.getId());
        pw.print(" -> rel");
        pw.print(rel.getId());
        if (relSubset.best == rel) {
          pw.print("[color=blue]");
        }
        pw.print(";");
        List<RelNode> inputs = rel.getInputs();
        for (int i = 0; i < inputs.size(); i++) {
          RelNode input = inputs.get(i);
          pw.print(" rel");
          pw.print(rel.getId());
          pw.print(" -> ");
          pw.print(input instanceof RelSubset ? "subset" : "rel");
          pw.print(input.getId());
          if (relSubset.best == rel || inputs.size() > 1) {
            char sep = '[';
            if (relSubset.best == rel) {
              pw.print(sep);
              pw.print("color=blue");
              sep = ',';
            }
            if (inputs.size() > 1) {
              pw.print(sep);
              pw.print("label=\"");
              pw.print(i);
              pw.print("\"");
              // sep = ',';
            }
            pw.print(']');
          }
          pw.print(";");
        }
        pw.println();
      }
    }

    // Draw lines for current rules
    for (VolcanoRuleCall ruleCall : ruleCallStack) {
      pw.print("rule");
      pw.print(ruleCall.id);
      pw.print(" [style=dashed,label=");
      Util.printJavaString(pw, ruleCall.rule.toString(), false);
      pw.print("]");

      RelNode[] rels = ruleCall.rels;
      for (int i = 0; i < rels.length; i++) {
        RelNode rel = rels[i];
        pw.print(" rule");
        pw.print(ruleCall.id);
        pw.print(" -> ");
        pw.print(rel instanceof RelSubset ? "subset" : "rel");
        pw.print(rel.getId());
        pw.print(" [style=dashed");
        if (rels.length > 1) {
          pw.print(",label=\"");
          pw.print(i);
          pw.print("\"");
        }
        pw.print("]");
        pw.print(";");
      }
      pw.println();
    }

    pw.print("}");
  }

  /**
   * Re-computes the digest of a {@link RelNode}.
   *
   * note: 重新计算 RelNode 的 digest，RelSet 会调用这个方法
   * note：这个 digest 包含它 children 的 identifiers，如果一个 child 已经 rename（比如其他 Subset 与其他做了 merge） 了，这个值需要重新计算
   * <p>Since a relational expression's digest contains the identifiers of its
   * children, this method needs to be called when the child has been renamed,
   * for example if the child's set merges with another.
   *
   * @param rel Relational expression
   */
  void rename(RelNode rel) {
    final String oldDigest = rel.getDigest();
    if (fixUpInputs(rel)) {
      final RelNode removed = mapDigestToRel.remove(oldDigest);
      assert removed == rel;
      final String newDigest = rel.recomputeDigest(); //note: 重新计算
      LOGGER.trace("Rename #{} from '{}' to '{}'", rel.getId(), oldDigest, newDigest);
      final RelNode equivRel = mapDigestToRel.put(newDigest, rel);
      if (equivRel != null) {
        assert equivRel != rel;

        // There's already an equivalent with the same name, and we
        // just knocked it out. Put it back, and forget about 'rel'.
        LOGGER.trace("After renaming rel#{} it is now equivalent to rel#{}",
            rel.getId(), equivRel.getId());

        assert RelOptUtil.equal(
            "rel rowtype",
            rel.getRowType(),
            "equivRel rowtype",
            equivRel.getRowType(),
            Litmus.THROW);

        mapDigestToRel.put(newDigest, equivRel);

        RelSubset equivRelSubset = getSubset(equivRel);
        ruleQueue.recompute(equivRelSubset, true);

        // Remove back-links from children.
        for (RelNode input : rel.getInputs()) {
          ((RelSubset) input).set.parents.remove(rel);
        }

        // Remove rel from its subset. (This may leave the subset
        // empty, but if so, that will be dealt with when the sets
        // get merged.)
        final RelSubset subset = mapRel2Subset.put(rel, equivRelSubset);
        assert subset != null;
        boolean existed = subset.set.rels.remove(rel);
        assert existed : "rel was not known to its set";
        final RelSubset equivSubset = getSubset(equivRel);
        if (equivSubset != subset) {
          // The equivalent relational expression is in a different
          // subset, therefore the sets are equivalent.
          assert equivSubset.getTraitSet().equals(
              subset.getTraitSet());
          assert equivSubset.set != subset.set;
          merge(equivSubset.set, subset.set);
        }
      }
    }
  }

  /**
   * Registers a {@link RelNode}, which has already been registered, in a new
   * {@link RelSet}.
   *
   * @param set Set
   * @param rel Relational expression
   */
  void reregister(
      RelSet set,
      RelNode rel) {
    // Is there an equivalent relational expression? (This might have
    // just occurred because the relational expression's child was just
    // found to be equivalent to another set.)
    RelNode equivRel = mapDigestToRel.get(rel.getDigest());
    if (equivRel != null && equivRel != rel) {
      assert equivRel.getClass() == rel.getClass();
      assert equivRel.getTraitSet().equals(rel.getTraitSet());
      assert RelOptUtil.equal(
          "rel rowtype",
          rel.getRowType(),
          "equivRel rowtype",
          equivRel.getRowType(),
          Litmus.THROW);

      RelSubset equivRelSubset = getSubset(equivRel);
      ruleQueue.recompute(equivRelSubset, true);
      return;
    }

    // Add the relational expression into the correct set and subset.
    RelSubset subset2 = addRelToSet(rel, set);
  }

  /**
   * If a subset has one or more equivalent subsets (owing to a set having
   * merged with another), returns the subset which is the leader of the
   * equivalence class.
   *
   * @param subset Subset
   * @return Leader of subset's equivalence class
   */
  private RelSubset canonize(final RelSubset subset) {
    if (subset.set.equivalentSet == null) {
      return subset;
    }
    RelSet set = subset.set;
    do {
      set = set.equivalentSet;
    } while (set.equivalentSet != null);
    return set.getOrCreateSubset(
        subset.getCluster(), subset.getTraitSet());
  }

  /**
   * Fires all rules matched by a relational expression.
   * note： 触发满足这个 relational expression 的所有 rules
   *
   * @param rel      Relational expression which has just been created (or maybe
   *                 from the queue)
   * @param deferred If true, each time a rule matches, just add an entry to
   *                 the queue.
   */
  void fireRules(
      RelNode rel,
      boolean deferred) {
    for (RelOptRuleOperand operand : classOperands.get(rel.getClass())) {
      if (operand.matches(rel)) { //note: rule 匹配的情况
        final VolcanoRuleCall ruleCall;
        if (deferred) { //note: 这里默认都是 true，会把 RuleMatch 添加到 queue 中
          ruleCall = new DeferringRuleCall(this, operand);
        } else {
          ruleCall = new VolcanoRuleCall(this, operand);
        }
        ruleCall.match(rel);
      }
    }
  }

  private boolean fixUpInputs(RelNode rel) {
    List<RelNode> inputs = rel.getInputs();
    int i = -1;
    int changeCount = 0;
    for (RelNode input : inputs) {
      ++i;
      if (input instanceof RelSubset) {
        final RelSubset subset = (RelSubset) input;
        RelSubset newSubset = canonize(subset);
        if (newSubset != subset) {
          rel.replaceInput(i, newSubset);
          if (subset.set != newSubset.set) {
            subset.set.parents.remove(rel);
            newSubset.set.parents.add(rel);
          }
          changeCount++;
        }
      }
    }
    return changeCount > 0;
  }

  private RelSet merge(RelSet set, RelSet set2) {
    assert set != set2 : "pre: set != set2";

    // Find the root of set2's equivalence tree.
    set = equivRoot(set);
    set2 = equivRoot(set2);

    // Looks like set2 was already marked as equivalent to set. Nothing
    // to do.
    if (set2 == set) {
      return set;
    }

    // If necessary, swap the sets, so we're always merging the newer set
    // into the older.
    if (set.id > set2.id) {
      RelSet t = set;
      set = set2;
      set2 = t;
    }

    // Merge.
    //note: merge 操作
    set.mergeWith(this, set2);

    // Was the set we merged with the root? If so, the result is the new
    // root.
    if (set2 == getSet(root)) {
      root =
          set.getOrCreateSubset(
              root.getCluster(),
              root.getTraitSet());
      ensureRootConverters();
    }

    return set;
  }

  private static RelSet equivRoot(RelSet s) {
    RelSet p = s; // iterates at twice the rate, to detect cycles
    while (s.equivalentSet != null) {
      p = forward2(s, p);
      s = s.equivalentSet;
    }
    return s;
  }

  /** Moves forward two links, checking for a cycle at each. */
  private static RelSet forward2(RelSet s, RelSet p) {
    p = forward1(s, p);
    p = forward1(s, p);
    return p;
  }

  /** Moves forward one link, checking for a cycle. */
  private static RelSet forward1(RelSet s, RelSet p) {
    if (p != null) {
      p = p.equivalentSet;
      if (p == s) {
        throw new AssertionError("cycle in equivalence tree");
      }
    }
    return p;
  }

  /**
   * Registers a new expression <code>exp</code> and queues up rule matches.
   * If <code>set</code> is not null, makes the expression part of that
   * equivalence set. If an identical expression is already registered, we
   * don't need to register this one and nor should we queue up rule matches.
   *
   * note：注册一个新的 expression；对 rule match 进行排队；
   * note：如果 set 不为 null，那么就使 expression 成为等价集合（RelSet）的一部分
   * note：rel：必须是 RelSubset 或者未注册的 RelNode
   * @param rel relational expression to register. Must be either a
   *         {@link RelSubset}, or an unregistered {@link RelNode}
   * @param set set that rel belongs to, or <code>null</code>
   * @return the equivalence-set
   */
  private RelSubset registerImpl(
      RelNode rel,
      RelSet set) {
    if (rel instanceof RelSubset) { //note: 如果是 RelSubset 类型，已经注册过了
      return registerSubset(set, (RelSubset) rel); //note: 做相应的 merge
    }

    assert !isRegistered(rel) : "already been registered: " + rel;
    if (rel.getCluster().getPlanner() != this) { //note: cluster 中 planner 与这里不同
      throw new AssertionError("Relational expression " + rel
          + " belongs to a different planner than is currently being used.");
    }

    // Now is a good time to ensure that the relational expression
    // implements the interface required by its calling convention.
    //note: 确保 relational expression 可以实施其 calling convention 所需的接口
    //note: 获取 RelNode 的 RelTraitSet
    final RelTraitSet traits = rel.getTraitSet();
    //note: 获取其 ConventionTraitDef
    final Convention convention = traits.getTrait(ConventionTraitDef.INSTANCE);
    assert convention != null;
    if (!convention.getInterface().isInstance(rel)
        && !(rel instanceof Converter)) {
      throw new AssertionError("Relational expression " + rel
          + " has calling-convention " + convention
          + " but does not implement the required interface '"
          + convention.getInterface() + "' of that convention");
    }
    if (traits.size() != traitDefs.size()) {
      throw new AssertionError("Relational expression " + rel
          + " does not have the correct number of traits: " + traits.size()
          + " != " + traitDefs.size());
    }

    // Ensure that its sub-expressions are registered.
    //note: 其实现在 AbstractRelNode 对应的方法中，实际上调用的还是 ensureRegistered 方法进行注册
    //note: 将 RelNode 的所有 inputs 注册到 planner 中
    //note: 这里会递归调用 registerImpl 注册 relNode 与 RelSet，直到其 inputs 全部注册
    //note: 返回的是一个 RelSubset 类型
    rel = rel.onRegister(this);

    // Record its provenance. (Rule call may be null.)
    //note: 记录 RelNode 的来源
    if (ruleCallStack.isEmpty()) { //note: 不知道来源时
      provenanceMap.put(rel, Provenance.EMPTY);
    } else { //note: 来自 rule 触发的情况
      final VolcanoRuleCall ruleCall = ruleCallStack.peek();
      provenanceMap.put(
          rel,
          new RuleProvenance(
              ruleCall.rule,
              ImmutableList.copyOf(ruleCall.rels),
              ruleCall.id));
    }

    // If it is equivalent to an existing expression, return the set that
    // the equivalent expression belongs to.
    //note: 根据 RelNode 的 digest（摘要，全局唯一）判断其是否已经有对应的 RelSubset，有的话直接放回
    String key = rel.getDigest();
    RelNode equivExp = mapDigestToRel.get(key);
    if (equivExp == null) { //note: 还没注册的情况
      // do nothing
    } else if (equivExp == rel) {//note: 已经有其缓存信息
      return getSubset(rel);
    } else {
      assert RelOptUtil.equal(
          "left", equivExp.getRowType(),
          "right", rel.getRowType(),
          Litmus.THROW);
      RelSet equivSet = getSet(equivExp); //note: 有 RelSubset 但对应的 RelNode 不同时，这里对其 RelSet 做下 merge
      if (equivSet != null) {
        LOGGER.trace(
            "Register: rel#{} is equivalent to {}", rel.getId(), equivExp.getDescription());
        return registerSubset(set, getSubset(equivExp));
      }
    }

    //note： Converters are in the same set as their children.
    if (rel instanceof Converter) {
      final RelNode input = ((Converter) rel).getInput();
      final RelSet childSet = getSet(input);
      if ((set != null)
          && (set != childSet)
          && (set.equivalentSet == null)) {
        LOGGER.trace(
            "Register #{} {} (and merge sets, because it is a conversion)",
            rel.getId(), rel.getDigest());
        merge(set, childSet);
        registerCount++;

        // During the mergers, the child set may have changed, and since
        // we're not registered yet, we won't have been informed. So
        // check whether we are now equivalent to an existing
        // expression.
        if (fixUpInputs(rel)) {
          rel.recomputeDigest();
          key = rel.getDigest();
          RelNode equivRel = mapDigestToRel.get(key);
          if ((equivRel != rel) && (equivRel != null)) {
            assert RelOptUtil.equal(
                "rel rowtype",
                rel.getRowType(),
                "equivRel rowtype",
                equivRel.getRowType(),
                Litmus.THROW);

            // make sure this bad rel didn't get into the
            // set in any way (fixupInputs will do this but it
            // doesn't know if it should so it does it anyway)
            set.obliterateRelNode(rel);

            // There is already an equivalent expression. Use that
            // one, and forget about this one.
            return getSubset(equivRel);
          }
        }
      } else {
        set = childSet;
      }
    }

    // Place the expression in the appropriate equivalence set.
    //note: 把 expression 放到合适的 等价集 中
    //note: 如果 RelSet 不存在，这里会初始化一个 RelSet
    if (set == null) {
      set = new RelSet(
          nextSetId++,
          Util.minus(
              RelOptUtil.getVariablesSet(rel),
              rel.getVariablesSet()),
          RelOptUtil.getVariablesUsed(rel));
      this.allSets.add(set);
    }

    // Chain to find 'live' equivalent set, just in case several sets are
    // merging at the same time.
    //note: 递归查询，一直找到最开始的 语义相等的集合，防止不同集合同时被 merge
    while (set.equivalentSet != null) {
      set = set.equivalentSet;
    }

    // Allow each rel to register its own rules.
    registerClass(rel);

    registerCount++;
    //note: 初始时是 0
    final int subsetBeforeCount = set.subsets.size();
    //note: 向等价集中添加相应的 RelNode，并更新其 best 信息
    RelSubset subset = addRelToSet(rel, set);

    //note: 缓存相关信息，返回的 key 之前对应的 value
    final RelNode xx = mapDigestToRel.put(key, rel);
    assert xx == null || xx == rel : rel.getDigest();

    LOGGER.trace("Register {} in {}", rel.getDescription(), subset.getDescription());

    // This relational expression may have been registered while we
    // recursively registered its children. If this is the case, we're done.
    if (xx != null) {
      return subset;
    }

    // Create back-links from its children, which makes children more
    // important.
    //note: 如果是 root，初始化其 importance 为 1.0
    if (rel == this.root) {
      ruleQueue.subsetImportances.put(
          subset,
          1.0); // todo: remove
    }
    //note: 将 Rel 的 input 对应的 RelSubset 的 parents 设置为当前的 Rel
    //note: 也就是说，一个 RelNode 的 input 为其对应 RelSubset 的 children 节点
    for (RelNode input : rel.getInputs()) {
      RelSubset childSubset = (RelSubset) input;
      childSubset.set.parents.add(rel);

      // Child subset is more important now a new parent uses it.
      //note: 重新计算 RelSubset 的 importance
      ruleQueue.recompute(childSubset);
    }
    if (rel == this.root) {// TODO: 2019-03-11 这里为什么要删除呢？
      ruleQueue.subsetImportances.remove(subset);
    }

    // Remember abstract converters until they're satisfied
    //note: 如果是 AbstractConverter 示例，添加到 abstractConverters 集合中
    if (rel instanceof AbstractConverter) {
      set.abstractConverters.add((AbstractConverter) rel);
    }

    // If this set has any unsatisfied converters, try to satisfy them.
    //note: check set.abstractConverters
    checkForSatisfiedConverters(set, rel);

    // Make sure this rel's subset importance is updated
    //note: 强制更新（重新计算） subset 的 importance
    ruleQueue.recompute(subset, true);

    //note: 触发所有匹配的 rule，这里是添加到对应的 RuleQueue 中
    // Queue up all rules triggered by this relexp's creation.
    fireRules(rel, true);

    // It's a new subset.
    //note: 如果是一个 new subset，再做一次触发
    if (set.subsets.size() > subsetBeforeCount) {
      fireRules(subset, true);
    }

    return subset;
  }

  //note: 向等价集中添加相应的 RelNode，并更新其 best 信息
  private RelSubset addRelToSet(RelNode rel, RelSet set) {
    RelSubset subset = set.add(rel);
    mapRel2Subset.put(rel, subset);

    // While a tree of RelNodes is being registered, sometimes nodes' costs
    // improve and the subset doesn't hear about it. You can end up with
    // a subset with a single rel of cost 99 which thinks its best cost is
    // 100. We think this happens because the back-links to parents are
    // not established. So, give the subset another change to figure out
    // its cost.
    //note: 当一个 RelNode tree 注册之后，有些情况下 nodes' cost 提高，但 subset 并不知道
    //note: 因为前面的 add 操作并没有触发 cost 计算操作，所以 subset 并不知道其 cost 是否已经进行了相应的优化
    //note: 这是可能发生的，因为现在它跟父节点的连接还没有建起来，所以，这里触发一下 subset，让其计算它的 cost
    //note：按照前面的调用顺序，这里会先调用其子节点（root 节点查找相应的 input 节点）
    final RelMetadataQuery mq = rel.getCluster().getMetadataQuery();
    //note: 向 RelSet 中添加完 RelNode 之后，这里会重新计算其 Cost 信息
    subset.propagateCostImprovements(this, mq, rel, new HashSet<>());

    return subset;
  }

  //note: 注册 RelSubset，做相应的 merge
  private RelSubset registerSubset(
      RelSet set,
      RelSubset subset) {
    if ((set != subset.set)
        && (set != null)
        && (set.equivalentSet == null)) {
      LOGGER.trace("Register #{} {}, and merge sets", subset.getId(), subset);
      merge(set, subset.set);
      registerCount++;
    }
    return subset;
  }

  // implement RelOptPlanner
  public void addListener(RelOptListener newListener) {
    // TODO jvs 6-Apr-2006:  new superclass AbstractRelOptPlanner
    // now defines a multicast listener; just need to hook it in
    if (listener != null) {
      throw Util.needToImplement("multiple VolcanoPlanner listeners");
    }
    listener = newListener;
  }

  // implement RelOptPlanner
  public void registerMetadataProviders(List<RelMetadataProvider> list) {
    list.add(0, new VolcanoRelMetadataProvider());
  }

  // implement RelOptPlanner
  public long getRelMetadataTimestamp(RelNode rel) {
    RelSubset subset = getSubset(rel);
    if (subset == null) {
      return 0;
    } else {
      return subset.timestamp;
    }
  }

  /**
   * Normalizes references to subsets within the string representation of a
   * plan.
   *
   * <p>This is useful when writing tests: it helps to ensure that tests don't
   * break when an extra rule is introduced that generates a new subset and
   * causes subsequent subset numbers to be off by one.
   *
   * <p>For example,
   *
   * <blockquote>
   * FennelAggRel.FENNEL_EXEC(child=Subset#17.FENNEL_EXEC,groupCount=1,
   * EXPR$1=COUNT())<br>
   * &nbsp;&nbsp;FennelSortRel.FENNEL_EXEC(child=Subset#2.FENNEL_EXEC,
   * key=[0], discardDuplicates=false)<br>
   * &nbsp;&nbsp;&nbsp;&nbsp;FennelCalcRel.FENNEL_EXEC(
   * child=Subset#4.FENNEL_EXEC, expr#0..8={inputs}, expr#9=3456,
   * DEPTNO=$t7, $f0=$t9)<br>
   * &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;MockTableImplRel.FENNEL_EXEC(
   * table=[CATALOG, SALES, EMP])</blockquote>
   *
   * <p>becomes
   *
   * <blockquote>
   * FennelAggRel.FENNEL_EXEC(child=Subset#{0}.FENNEL_EXEC, groupCount=1,
   * EXPR$1=COUNT())<br>
   * &nbsp;&nbsp;FennelSortRel.FENNEL_EXEC(child=Subset#{1}.FENNEL_EXEC,
   * key=[0], discardDuplicates=false)<br>
   * &nbsp;&nbsp;&nbsp;&nbsp;FennelCalcRel.FENNEL_EXEC(
   * child=Subset#{2}.FENNEL_EXEC,expr#0..8={inputs},expr#9=3456,DEPTNO=$t7,
   * $f0=$t9)<br>
   * &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;MockTableImplRel.FENNEL_EXEC(
   * table=[CATALOG, SALES, EMP])</blockquote>
   *
   * @param plan Plan
   * @return Normalized plan
   */
  public static String normalizePlan(String plan) {
    if (plan == null) {
      return null;
    }
    final Pattern poundDigits = Pattern.compile("Subset#[0-9]+\\.");
    int i = 0;
    while (true) {
      final Matcher matcher = poundDigits.matcher(plan);
      if (!matcher.find()) {
        return plan;
      }
      final String token = matcher.group(); // e.g. "Subset#23."
      plan = plan.replace(token, "Subset#{" + i++ + "}.");
    }
  }

  /**
   * Sets whether this planner is locked. A locked planner does not accept
   * new rules. {@link #addRule(org.apache.calcite.plan.RelOptRule)} will do
   * nothing and return false.
   *
   * @param locked Whether planner is locked
   */
  public void setLocked(boolean locked) {
    this.locked = locked;
  }

  public void ensureRegistered(
      RelNode rel,
      RelNode equivRel,
      VolcanoRuleCall ruleCall) {
    ensureRegistered(rel, equivRel);
  }

  //~ Inner Classes ----------------------------------------------------------

  /**
   * A rule call which defers its actions. Whereas {@link RelOptRuleCall}
   * invokes the rule when it finds a match, a <code>DeferringRuleCall</code>
   * creates a {@link VolcanoRuleMatch} which can be invoked later.
   */
  private static class DeferringRuleCall extends VolcanoRuleCall {
    DeferringRuleCall(
        VolcanoPlanner planner,
        RelOptRuleOperand operand) {
      super(planner, operand);
    }

    /**
     * Rather than invoking the rule (as the base method does), creates a
     * {@link VolcanoRuleMatch} which can be invoked later.
     * note：不是直接触发 rule，而是创建一个后续可以被触发的 VolcanoRuleMatch
     */
    protected void onMatch() {
      final VolcanoRuleMatch match =
          new VolcanoRuleMatch(
              volcanoPlanner,
              getOperand0(), //note: 其实就是 operand
              rels,
              nodeInputs);
      volcanoPlanner.ruleQueue.addMatch(match);
    }
  }

  /**
   * Where a RelNode came from.
   */
  private abstract static class Provenance {
    public static final Provenance EMPTY = new UnknownProvenance();
  }

  /**
   * We do not know where this RelNode came from. Probably created by hand,
   * or by sql-to-rel converter.
   * note：不知道来源时
   */
  private static class UnknownProvenance extends Provenance {
  }

  /**
   * A RelNode that came directly from another RelNode via a copy.
   * note：来自直接另一个 RelNode 的 copy
   */
  static class DirectProvenance extends Provenance {
    final RelNode source;

    DirectProvenance(RelNode source) {
      this.source = source;
    }
  }

  /**
   * A RelNode that came via the firing of a rule.
   * note：来自 rule 的触发，记录相关的信息
   */
  static class RuleProvenance extends Provenance {
    final RelOptRule rule;
    final ImmutableList<RelNode> rels;
    final int callId;

    RuleProvenance(RelOptRule rule, ImmutableList<RelNode> rels, int callId) {
      this.rule = rule;
      this.rels = rels;
      this.callId = callId;
    }
  }
}

// End VolcanoPlanner.java
