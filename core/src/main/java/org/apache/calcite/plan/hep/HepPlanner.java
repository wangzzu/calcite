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
package org.apache.calcite.plan.hep;

import org.apache.calcite.linq4j.function.Function2;
import org.apache.calcite.linq4j.function.Functions;
import org.apache.calcite.plan.AbstractRelOptPlanner;
import org.apache.calcite.plan.CommonRelSubExprRule;
import org.apache.calcite.plan.Context;
import org.apache.calcite.plan.RelOptCost;
import org.apache.calcite.plan.RelOptCostFactory;
import org.apache.calcite.plan.RelOptCostImpl;
import org.apache.calcite.plan.RelOptMaterialization;
import org.apache.calcite.plan.RelOptPlanner;
import org.apache.calcite.plan.RelOptRule;
import org.apache.calcite.plan.RelOptRuleOperand;
import org.apache.calcite.plan.RelTrait;
import org.apache.calcite.plan.RelTraitSet;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.convert.Converter;
import org.apache.calcite.rel.convert.ConverterRule;
import org.apache.calcite.rel.convert.TraitMatchingRule;
import org.apache.calcite.rel.core.RelFactories;
import org.apache.calcite.rel.metadata.RelMetadataProvider;
import org.apache.calcite.rel.metadata.RelMetadataQuery;
import org.apache.calcite.util.Pair;
import org.apache.calcite.util.Util;
import org.apache.calcite.util.graph.BreadthFirstIterator;
import org.apache.calcite.util.graph.CycleDetector;
import org.apache.calcite.util.graph.DefaultDirectedGraph;
import org.apache.calcite.util.graph.DefaultEdge;
import org.apache.calcite.util.graph.DepthFirstIterator;
import org.apache.calcite.util.graph.DirectedGraph;
import org.apache.calcite.util.graph.Graphs;
import org.apache.calcite.util.graph.TopologicalOrderIterator;

import com.google.common.collect.ImmutableList;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * HepPlanner is a heuristic implementation of the {@link RelOptPlanner}
 * interface.
 */
public class HepPlanner extends AbstractRelOptPlanner {
  //~ Instance fields --------------------------------------------------------

  private final HepProgram mainProgram;

  private HepProgram currentProgram;

  private HepRelVertex root; //note: root HepRelVertex

  private RelTraitSet requestedRootTraits;

  private final Map<String, HepRelVertex> mapDigestToVertex = new HashMap<>();

  // NOTE jvs 24-Apr-2006:  We use LinkedHashSet
  // in order to provide deterministic behavior.
  private final Set<RelOptRule> allRules = new LinkedHashSet<>();//note: 记录注册的 Rules 信息

  private int nTransformations;

  private int graphSizeLastGC;

  private int nTransformationsLastGC;

  private final boolean noDag;

  /**
   * Query graph, with edges directed from parent to child. This is a
   * single-rooted DAG, possibly with additional roots corresponding to
   * discarded plan fragments which remain to be garbage-collected.
   * 这里的 Graph 就是一个节点
   */
  private final DirectedGraph<HepRelVertex, DefaultEdge> graph =
      DefaultDirectedGraph.create();

  private final Function2<RelNode, RelNode, Void> onCopyHook;

  private final List<RelOptMaterialization> materializations =
      new ArrayList<>();

  //~ Constructors -----------------------------------------------------------

  /**
   * Creates a new HepPlanner that allows DAG.
   *
   * @param program program controlling rule application
   */
  public HepPlanner(HepProgram program) {
    this(program, null, false, null, RelOptCostImpl.FACTORY);
  }

  /**
   * Creates a new HepPlanner that allows DAG.
   *
   * @param program program controlling rule application
   * @param context to carry while planning
   */
  public HepPlanner(HepProgram program, Context context) {
    this(program, context, false, null, RelOptCostImpl.FACTORY);
  }

  /**
   * Creates a new HepPlanner with the option to keep the graph a
   * tree (noDag = true) or allow DAG (noDag = false).
   *
   * @param noDag      If false, create shared nodes if expressions are
   *                   identical
   * @param program    Program controlling rule application
   * @param onCopyHook Function to call when a node is copied
   */
  public HepPlanner(
      HepProgram program,
      Context context,
      boolean noDag,
      Function2<RelNode, RelNode, Void> onCopyHook,
      RelOptCostFactory costFactory) {
    super(costFactory, context);
    this.mainProgram = program;
    this.onCopyHook = Util.first(onCopyHook, Functions.ignore2());
    this.noDag = noDag; //note: false，允许使用 DAG 封装（为 true 时，还是 tree 的形式）
  }

  //~ Methods ----------------------------------------------------------------

  // implement RelOptPlanner
  //note: Sets the root node of this query.
  public void setRoot(RelNode rel) {
    //note: 将 RelNode 转换为 DAG 表示
    root = addRelToGraph(rel);
    //note: 仅仅是在 trace 日志中输出 Graph 信息
    dumpGraph();
  }

  // implement RelOptPlanner
  public RelNode getRoot() {
    return root;
  }

  public List<RelOptRule> getRules() {
    return ImmutableList.copyOf(allRules);
  }

  // implement RelOptPlanner
  //note: 注册 Rule 到
  public boolean addRule(RelOptRule rule) {
    boolean added = allRules.add(rule);
    if (added) {
      mapRuleDescription(rule);
    }
    return added;
  }

  @Override public void clear() {
    super.clear();
    for (RelOptRule rule : ImmutableList.copyOf(allRules)) {
      removeRule(rule);
    }
    this.materializations.clear();
  }

  public boolean removeRule(RelOptRule rule) {
    unmapRuleDescription(rule);
    return allRules.remove(rule);
  }

  // implement RelOptPlanner
  public RelNode changeTraits(RelNode rel, RelTraitSet toTraits) {
    // Ignore traits, except for the root, where we remember
    // what the final conversion should be.
    if ((rel == root) || (rel == root.getCurrentRel())) {
      requestedRootTraits = toTraits;
    }
    return rel;
  }

  // implement RelOptPlanner
  //note: 优化器的核心，匹配规则进行优化
  public RelNode findBestExp() {
    assert root != null;

    //note: 运行 HepProgram 算法(按 HepProgram 中的 instructions 进行相应的优化)
    executeProgram(mainProgram);

    // Get rid of everything except what's in the final plan.
    //note: 垃圾收集
    collectGarbage();

    return buildFinalPlan(root); //note: 返回最后的结果，还是以 RelNode 表示
  }

  private void executeProgram(HepProgram program) {
    HepProgram savedProgram = currentProgram; //note: 保留当前的 Program
    currentProgram = program;
    currentProgram.initialize(program == mainProgram);//note: 如果是在同一个 Program 的话，保留上次 cache
    for (HepInstruction instruction : currentProgram.instructions) {
      instruction.execute(this); //note: 按 Rule 进行优化(会调用 executeInstruction 方法)
      int delta = nTransformations - nTransformationsLastGC;
      if (delta > graphSizeLastGC) {
        // The number of transformations performed since the last
        // garbage collection is greater than the number of vertices in
        // the graph at that time.  That means there should be a
        // reasonable amount of garbage to collect now.  We do it this
        // way to amortize garbage collection cost over multiple
        // instructions, while keeping the highwater memory usage
        // proportional to the graph size.
        //note: 进行转换的次数已经大于 DAG Graph 中的顶点数，这就意味着已经产生大量垃圾需要进行清理
        collectGarbage();
      }
    }
    currentProgram = savedProgram;
  }

  //note: 获取初始化的 matchLimit
  void executeInstruction(
      HepInstruction.MatchLimit instruction) {
    LOGGER.trace("Setting match limit to {}", instruction.limit);
    currentProgram.matchLimit = instruction.limit;
  }

  void executeInstruction(
      HepInstruction.MatchOrder instruction) {
    LOGGER.trace("Setting match order to {}", instruction.order);
    currentProgram.matchOrder = instruction.order;
  }

  //note: 执行相应的 RuleInstance
  void executeInstruction(
      HepInstruction.RuleInstance instruction) {
    if (skippingGroup()) {
      return;
    }
    if (instruction.rule == null) {//note: 如果 rule 为 null，那么就按照 description 查找具体的 rule
      assert instruction.ruleDescription != null;
      instruction.rule =
          getRuleByDescription(instruction.ruleDescription);
      LOGGER.trace("Looking up rule with description {}, found {}",
          instruction.ruleDescription, instruction.rule);
    }
    //note: 执行相应的 rule
    if (instruction.rule != null) {
      applyRules(
          Collections.singleton(instruction.rule),
          true);
    }
  }

  void executeInstruction(
      HepInstruction.RuleClass<?> instruction) {
    if (skippingGroup()) {
      return;
    }
    LOGGER.trace("Applying rule class {}", instruction.ruleClass);
    if (instruction.ruleSet == null) {
      instruction.ruleSet = new LinkedHashSet<>();
      for (RelOptRule rule : allRules) {
        if (instruction.ruleClass.isInstance(rule)) {
          instruction.ruleSet.add(rule);
        }
      }
    }
    applyRules(instruction.ruleSet, true);
  }

  void executeInstruction(
      HepInstruction.RuleCollection instruction) {
    if (skippingGroup()) {
      return;
    }
    applyRules(instruction.rules, true);
  }

  private boolean skippingGroup() {
    if (currentProgram.group != null) {
      // Skip if we've already collected the ruleset.
      return !currentProgram.group.collecting;
    } else { //note: 默认初始化的值是 null
      // Not grouping.
      return false;
    }
  }

  void executeInstruction(
      HepInstruction.ConverterRules instruction) {
    assert currentProgram.group == null;
    if (instruction.ruleSet == null) {
      instruction.ruleSet = new LinkedHashSet<>();
      for (RelOptRule rule : allRules) {
        if (!(rule instanceof ConverterRule)) {
          continue;
        }
        ConverterRule converter = (ConverterRule) rule;
        if (converter.isGuaranteed() != instruction.guaranteed) {
          continue;
        }

        // Add the rule itself to work top-down
        instruction.ruleSet.add(converter);
        if (!instruction.guaranteed) {
          // Add a TraitMatchingRule to work bottom-up
          instruction.ruleSet.add(
              new TraitMatchingRule(converter, RelFactories.LOGICAL_BUILDER));
        }
      }
    }
    applyRules(instruction.ruleSet, instruction.guaranteed);
  }

  void executeInstruction(HepInstruction.CommonRelSubExprRules instruction) {
    assert currentProgram.group == null;
    if (instruction.ruleSet == null) {
      instruction.ruleSet = new LinkedHashSet<>();
      for (RelOptRule rule : allRules) {
        if (!(rule instanceof CommonRelSubExprRule)) {
          continue;
        }
        instruction.ruleSet.add(rule);
      }
    }
    applyRules(instruction.ruleSet, true);
  }

  void executeInstruction(
      HepInstruction.Subprogram instruction) {
    LOGGER.trace("Entering subprogram");
    for (;;) {
      int nTransformationsBefore = nTransformations;
      executeProgram(instruction.subprogram);
      if (nTransformations == nTransformationsBefore) {
        // Nothing happened this time around.
        break;
      }
    }
    LOGGER.trace("Leaving subprogram");
  }

  void executeInstruction(
      HepInstruction.BeginGroup instruction) {
    assert currentProgram.group == null;
    currentProgram.group = instruction.endGroup;
    LOGGER.trace("Entering group");
  }

  void executeInstruction(
      HepInstruction.EndGroup instruction) {
    assert currentProgram.group == instruction;
    currentProgram.group = null;
    instruction.collecting = false;
    applyRules(instruction.ruleSet, true);
    LOGGER.trace("Leaving group");
  }

  //note: 深度优先这种顺序的情况下，做相应的 rule 匹配
  private int depthFirstApply(Iterator<HepRelVertex> iter,
      Collection<RelOptRule> rules,
      boolean forceConversions, int nMatches) {
    while (iter.hasNext()) {
      HepRelVertex vertex = iter.next();
      for (RelOptRule rule : rules) {
        HepRelVertex newVertex =
            applyRule(rule, vertex, forceConversions); //note: 匹配
        if (newVertex == null || newVertex == vertex) {
          continue;
        }
        ++nMatches;
        if (nMatches >= currentProgram.matchLimit) {
          return nMatches;
        }
        // To the extent possible, pick up where we left
        // off; have to create a new iterator because old
        // one was invalidated by transformation.
        Iterator<HepRelVertex> depthIter = getGraphIterator(newVertex);
        nMatches = depthFirstApply(depthIter, rules, forceConversions,
            nMatches);
        break;
      }
    }
    return nMatches;
  }

  //note: 执行 rule（forceConversions 默认 true）
  private void applyRules(
      Collection<RelOptRule> rules,
      boolean forceConversions) {
    if (currentProgram.group != null) {
      assert currentProgram.group.collecting;
      currentProgram.group.ruleSet.addAll(rules);
      return;
    }

    LOGGER.trace("Applying rule set {}", rules);

    //note: 当遍历规则是 ARBITRARY 或 DEPTH_FIRST 时，设置为 false，此时不会从 root 节点开始，否则每次 restart 都从 root 节点开始
    boolean fullRestartAfterTransformation =
        currentProgram.matchOrder != HepMatchOrder.ARBITRARY
        && currentProgram.matchOrder != HepMatchOrder.DEPTH_FIRST;

    int nMatches = 0;

    boolean fixedPoint;
    //note: 两种情况会跳出循环，一种是达到 matchLimit 限制，一种是遍历一遍不会再有新的 transform 产生
    do {
      //note: 按照遍历规则获取迭代器
      Iterator<HepRelVertex> iter = getGraphIterator(root);
      fixedPoint = true;
      while (iter.hasNext()) {
        HepRelVertex vertex = iter.next();//note: 遍历每个 HepRelVertex
        for (RelOptRule rule : rules) {//note: 遍历每个 rules
          //note: 进行规制匹配，也是真正进行相关操作的地方
          HepRelVertex newVertex =
              applyRule(rule, vertex, forceConversions);
          if (newVertex == null || newVertex == vertex) {
            continue;
          }
          ++nMatches;
          //note: 超过 MatchLimit 的限制
          if (nMatches >= currentProgram.matchLimit) {
            return;
          }
          if (fullRestartAfterTransformation) {
            //note: 发生 transformation 后，从 root 节点再次开始
            iter = getGraphIterator(root);
          } else {
            // To the extent possible, pick up where we left
            // off; have to create a new iterator because old
            // one was invalidated by transformation.
            //note: 尽可能从上次进行后的节点开始
            iter = getGraphIterator(newVertex);
            if (currentProgram.matchOrder == HepMatchOrder.DEPTH_FIRST) {
              //note: 这样做的原因就是为了防止有些 HepRelVertex 遗漏了 rule 的匹配（每次从 root 开始是最简单的算法），因为可能出现下推
              nMatches =
                  depthFirstApply(iter, rules, forceConversions, nMatches);
              if (nMatches >= currentProgram.matchLimit) {
                return;
              }
            }
            // Remember to go around again since we're
            // skipping some stuff.
            //note: 再来一遍，因为前面有跳过一些内容
            fixedPoint = false;
          }
          break;
        }
      }
    } while (!fixedPoint);
  }

  private Iterator<HepRelVertex> getGraphIterator(HepRelVertex start) {
    // Make sure there's no garbage, because topological sort
    // doesn't start from a specific root, and rules can't
    // deal with firing on garbage.

    // FIXME jvs 25-Sept-2006:  I had to move this earlier because
    // of FRG-215, which is still under investigation.  Once we
    // figure that one out, move down to location below for
    // better optimizer performance.
    collectGarbage();

    switch (currentProgram.matchOrder) {
    case ARBITRARY:
    case DEPTH_FIRST:
      return DepthFirstIterator.of(graph, start).iterator();

    case TOP_DOWN:
      assert start == root;
      // see above
/*
        collectGarbage();
*/
      return TopologicalOrderIterator.of(graph).iterator();

    case BOTTOM_UP:
    default:
      assert start == root;

      // see above
/*
        collectGarbage();
*/

      // TODO jvs 4-Apr-2006:  enhance TopologicalOrderIterator
      // to support reverse walk.
      final List<HepRelVertex> list = new ArrayList<>();
      for (HepRelVertex vertex : TopologicalOrderIterator.of(graph)) {
        list.add(vertex);
      }
      Collections.reverse(list);
      return list.iterator();
    }
  }

  /** Returns whether the vertex is valid. */
  private boolean belongsToDag(HepRelVertex vertex) {
    String digest = vertex.getCurrentRel().getDigest();
    return mapDigestToVertex.get(digest) != null;
  }

  //note: rule 匹配操作的地方
  private HepRelVertex applyRule(
      RelOptRule rule,
      HepRelVertex vertex,
      boolean forceConversions) {
    if (!belongsToDag(vertex)) {//note: 这个 vertex 是否在当前的 dag 中（根据 digest 查找）
      return null;
    }
    RelTrait parentTrait = null;
    List<RelNode> parents = null;
    if (rule instanceof ConverterRule) {//note: ConverterRule的情况
      // Guaranteed converter rules require special casing to make sure
      // they only fire where actually needed, otherwise they tend to
      // fire to infinity and beyond.
      //note: 保证 converter 可以触发
      ConverterRule converterRule = (ConverterRule) rule;
      //note: isGuaranteed代表可以可以 converter，forceConversions 代表强制进行 converter
      if (converterRule.isGuaranteed() || !forceConversions) {
        if (!doesConverterApply(converterRule, vertex)) {
          return null;
        }
        parentTrait = converterRule.getOutTrait(); //note: 父节点的这个 Trait
      }
    } else if (rule instanceof CommonRelSubExprRule) {//note: CommonRelSubExprRule的情况
      // Only fire CommonRelSubExprRules if the vertex is a common
      // subexpression.
      List<HepRelVertex> parentVertices = getVertexParents(vertex);
      if (parentVertices.size() < 2) {
        return null;
      }
      parents = new ArrayList<>();
      for (HepRelVertex pVertex : parentVertices) {
        parents.add(pVertex.getCurrentRel());
      }
    }

    final List<RelNode> bindings = new ArrayList<>();
    final Map<RelNode, List<RelNode>> nodeChildren = new HashMap<>();
    //note: 判断是否 match
    boolean match =
        matchOperands(
            rule.getOperand(),
            vertex.getCurrentRel(),
            bindings,
            nodeChildren);

    if (!match) {
      return null;
    }

    HepRuleCall call =
        new HepRuleCall(
            this,
            rule.getOperand(),
            bindings.toArray(new RelNode[0]),
            nodeChildren,
            parents);

    // Allow the rule to apply its own side-conditions.
    if (!rule.matches(call)) {
      return null;
    }

    fireRule(call); //note: 触发 rule

    if (!call.getResults().isEmpty()) {
      return applyTransformationResults(
          vertex, //note: 原来的 vertex
          call, //note: HepRuleCall 中的 results 会记录 transform 的结果
          parentTrait);
    }

    return null;
  }

  private boolean doesConverterApply(
      ConverterRule converterRule,
      HepRelVertex vertex) {
    RelTrait outTrait = converterRule.getOutTrait();
    List<HepRelVertex> parents = Graphs.predecessorListOf(graph, vertex);
    for (HepRelVertex parent : parents) {
      RelNode parentRel = parent.getCurrentRel();
      if (parentRel instanceof Converter) {
        // We don't support converter chains.
        continue;
      }
      //note: 查看当前的 RelNode 父节点的 TraitSet 是否包含 outTrait（证明父节点是期望做这个转换的）
      if (parentRel.getTraitSet().contains(outTrait)) {
        // This parent wants the traits produced by the converter.
        return true;
      }
    }
    return (vertex == root)
        && (requestedRootTraits != null)
        && requestedRootTraits.contains(outTrait);
  }

  /**
   * Retrieves the parent vertices of a vertex.  If a vertex appears multiple
   * times as an input into a parent, then that counts as multiple parents,
   * one per input reference.
   *
   * @param vertex the vertex
   * @return the list of parents for the vertex
   */
  private List<HepRelVertex> getVertexParents(HepRelVertex vertex) {
    final List<HepRelVertex> parents = new ArrayList<>();
    final List<HepRelVertex> parentVertices =
        Graphs.predecessorListOf(graph, vertex);

    for (HepRelVertex pVertex : parentVertices) {
      RelNode parent = pVertex.getCurrentRel();
      for (int i = 0; i < parent.getInputs().size(); i++) {
        HepRelVertex child = (HepRelVertex) parent.getInputs().get(i);
        if (child == vertex) {
          parents.add(pVertex);
        }
      }
    }
    return parents;
  }

  //note:
  private boolean matchOperands(
      RelOptRuleOperand operand,
      RelNode rel,
      List<RelNode> bindings,
      Map<RelNode, List<RelNode>> nodeChildren) {
    if (!operand.matches(rel)) {
      return false;
    }
    bindings.add(rel); //note: 添加到 bindings
    @SuppressWarnings("unchecked")
    List<HepRelVertex> childRels = (List) rel.getInputs();
    switch (operand.childPolicy) {
    case ANY:
      return true;
    case UNORDERED:
      // For each operand, at least one child must match. If
      // matchAnyChildren, usually there's just one operand.
      for (RelOptRuleOperand childOperand : operand.getChildOperands()) {
        boolean match = false;
        for (HepRelVertex childRel : childRels) {
          match =
              matchOperands(
                  childOperand,
                  childRel.getCurrentRel(),
                  bindings,
                  nodeChildren);
          if (match) {
            break;
          }
        }
        if (!match) {
          return false;
        }
      }
      final List<RelNode> children = new ArrayList<>(childRels.size());
      for (HepRelVertex childRel : childRels) {
        children.add(childRel.getCurrentRel());
      }
      nodeChildren.put(rel, children);
      return true;
    default:
      int n = operand.getChildOperands().size();
      if (childRels.size() < n) {
        return false;
      }
      for (Pair<HepRelVertex, RelOptRuleOperand> pair
          : Pair.zip(childRels, operand.getChildOperands())) {
        boolean match =
            matchOperands(
                pair.right,
                pair.left.getCurrentRel(),
                bindings,
                nodeChildren);
        if (!match) {
          return false;
        }
      }
      return true;
    }
  }

  private HepRelVertex applyTransformationResults(
      HepRelVertex vertex,
      HepRuleCall call,
      RelTrait parentTrait) {
    // TODO jvs 5-Apr-2006:  Take the one that gives the best
    // global cost rather than the best local cost.  That requires
    // "tentative" graph edits.

    assert !call.getResults().isEmpty();

    RelNode bestRel = null;

    if (call.getResults().size() == 1) {//note: 只有一个生成计划
      // No costing required; skip it to minimize the chance of hitting
      // rels without cost information.
      bestRel = call.getResults().get(0);
    } else {
      RelOptCost bestCost = null;
      final RelMetadataQuery mq = call.getMetadataQuery();
      for (RelNode rel : call.getResults()) {
        RelOptCost thisCost = getCost(rel, mq);
        if (LOGGER.isTraceEnabled()) {
          // Keep in the isTraceEnabled for the getRowCount method call
          LOGGER.trace("considering {} with cumulative cost={} and rowcount={}",
              rel, thisCost, mq.getRowCount(rel));
        }
        if ((bestRel == null) || thisCost.isLt(bestCost)) { //note: 如果 cost 比 bestCost 少
          bestRel = rel;
          bestCost = thisCost;//note: 更新 bestCost
        }
      }
    }

    ++nTransformations;
    notifyTransformation(
        call,
        bestRel,
        true);

    // Before we add the result, make a copy of the list of vertex's
    // parents.  We'll need this later during contraction so that
    // we only update the existing parents, not the new parents
    // (otherwise loops can result).  Also take care of filtering
    // out parents by traits in case we're dealing with a converter rule.
    final List<HepRelVertex> allParents =
        Graphs.predecessorListOf(graph, vertex);
    final List<HepRelVertex> parents = new ArrayList<>();
    for (HepRelVertex parent : allParents) {
      if (parentTrait != null) {
        RelNode parentRel = parent.getCurrentRel();
        if (parentRel instanceof Converter) {
          // We don't support automatically chaining conversions.
          // Treating a converter as a candidate parent here
          // can cause the "iParentMatch" check below to
          // throw away a new converter needed in
          // the multi-parent DAG case.
          continue;
        }
        if (!parentRel.getTraitSet().contains(parentTrait)) {
          // This parent does not want the converted result.
          continue;
        }
      }
      parents.add(parent);
    }

    HepRelVertex newVertex = addRelToGraph(bestRel);

    // There's a chance that newVertex is the same as one
    // of the parents due to common subexpression recognition
    // (e.g. the LogicalProject added by JoinCommuteRule).  In that
    // case, treat the transformation as a nop to avoid
    // creating a loop.
    int iParentMatch = parents.indexOf(newVertex);
    if (iParentMatch != -1) {
      newVertex = parents.get(iParentMatch);
    } else {
      contractVertices(newVertex, vertex, parents);
    }

    if (getListener() != null) {
      // Assume listener doesn't want to see garbage.
      collectGarbage();
    }

    notifyTransformation(
        call,
        bestRel,
        false);

    dumpGraph();

    return newVertex;
  }

  // implement RelOptPlanner
  public RelNode register(
      RelNode rel,
      RelNode equivRel) {
    // Ignore; this call is mostly to tell Volcano how to avoid
    // infinite loops.
    return rel;
  }

  //note: 默认情况下，什么也不会做
  @Override public void onCopy(RelNode rel, RelNode newRel) {
    onCopyHook.apply(rel, newRel);
  }

  // implement RelOptPlanner
  public RelNode ensureRegistered(RelNode rel, RelNode equivRel) {
    return rel;
  }

  // implement RelOptPlanner
  public boolean isRegistered(RelNode rel) {
    return true;
  }

  //note: 根据 RelNode 构建一个 Graph
  private HepRelVertex addRelToGraph(
      RelNode rel) {
    // Check if a transformation already produced a reference
    // to an existing vertex.
    //note: 检查这个 rel 是否在 graph 中转换了
    if (graph.vertexSet().contains(rel)) {
      return (HepRelVertex) rel;
    }

    // Recursively add children, replacing this rel's inputs
    // with corresponding child vertices.
    //note: 递归地增加子节点，使用子节点相关的 vertices 代替 rel 的 input
    final List<RelNode> inputs = rel.getInputs();
    final List<RelNode> newInputs = new ArrayList<>();
    for (RelNode input1 : inputs) {
      HepRelVertex childVertex = addRelToGraph(input1); //note: 递归进行转换
      newInputs.add(childVertex); //note: 每个 HepRelVertex 只记录其 Input
    }

    if (!Util.equalShallow(inputs, newInputs)) { //note: 不相等的情况下
      RelNode oldRel = rel;
      rel = rel.copy(rel.getTraitSet(), newInputs);
      onCopy(oldRel, rel);
    }
    // Compute digest first time we add to DAG,
    // otherwise can't get equivVertex for common sub-expression
    //note: 计算 relNode 的 digest
    //note: Digest 的意思是：
    //note: A short description of this relational expression's type, inputs, and
    //note: other properties. The string uniquely identifies the node; another node
    //note: is equivalent if and only if it has the same value.
    rel.recomputeDigest();

    // try to find equivalent rel only if DAG is allowed
    //note: 如果允许 DAG 的话，检查是否有一个等价的 HepRelVertex，有的话直接返回
    if (!noDag) {
      // Now, check if an equivalent vertex already exists in graph.
      String digest = rel.getDigest();
      HepRelVertex equivVertex = mapDigestToVertex.get(digest);
      if (equivVertex != null) { //note: 已经存在
        // Use existing vertex.
        return equivVertex;
      }
    }

    // No equivalence:  create a new vertex to represent this rel.
    //note: 创建一个 vertex 代替 rel
    HepRelVertex newVertex = new HepRelVertex(rel);
    graph.addVertex(newVertex); //note: 记录 Vertex
    updateVertex(newVertex, rel);//note: 更新相关的缓存，比如 mapDigestToVertex map

    for (RelNode input : rel.getInputs()) { //note: 设置 Edge
      graph.addEdge(newVertex, (HepRelVertex) input);//note: 记录与整个 Vertex 先关的 input
    }

    nTransformations++;
    return newVertex;
  }

  private void contractVertices(
      HepRelVertex preservedVertex,
      HepRelVertex discardedVertex,
      List<HepRelVertex> parents) {
    if (preservedVertex == discardedVertex) {
      // Nop.
      return;
    }

    RelNode rel = preservedVertex.getCurrentRel();
    updateVertex(preservedVertex, rel);

    // Update specified parents of discardedVertex.
    for (HepRelVertex parent : parents) {
      RelNode parentRel = parent.getCurrentRel();
      List<RelNode> inputs = parentRel.getInputs();
      for (int i = 0; i < inputs.size(); ++i) {
        RelNode child = inputs.get(i);
        if (child != discardedVertex) {
          continue;
        }
        parentRel.replaceInput(i, preservedVertex);
      }
      graph.removeEdge(parent, discardedVertex);
      graph.addEdge(parent, preservedVertex);
      updateVertex(parent, parentRel);
    }

    // NOTE:  we don't actually do graph.removeVertex(discardedVertex),
    // because it might still be reachable from preservedVertex.
    // Leave that job for garbage collection.

    if (discardedVertex == root) {
      root = preservedVertex;
    }
  }

  private void updateVertex(HepRelVertex vertex, RelNode rel) {
    if (rel != vertex.getCurrentRel()) {
      // REVIEW jvs 5-Apr-2006:  We'll do this again later
      // during garbage collection.  Or we could get rid
      // of mark/sweep garbage collection and do it precisely
      // at this point by walking down to all rels which are only
      // reachable from here.
      notifyDiscard(vertex.getCurrentRel());
    }
    String oldDigest = vertex.getCurrentRel().toString();
    if (mapDigestToVertex.get(oldDigest) == vertex) {
      mapDigestToVertex.remove(oldDigest);
    }
    String newDigest = rel.getDigest();
    // When a transformation happened in one rule apply, support
    // vertex2 replace vertex1, but the current relNode of
    // vertex1 and vertex2 is same,
    // then the digest is also same. but we can't remove vertex2,
    // otherwise the digest will be removed wrongly in the mapDigestToVertex
    //  when collectGC
    // so it must update the digest that map to vertex
    mapDigestToVertex.put(newDigest, vertex);
    if (rel != vertex.getCurrentRel()) {
      vertex.replaceRel(rel);
    }
    notifyEquivalence(
        rel,
        vertex,
        false);
  }

  //note: 生成最后的计划， 还是以 RelNode 的形式展示
  private RelNode buildFinalPlan(HepRelVertex vertex) {
    RelNode rel = vertex.getCurrentRel();

    notifyChosen(rel);

    // Recursively process children, replacing this rel's inputs
    // with corresponding child rels.
    List<RelNode> inputs = rel.getInputs();
    for (int i = 0; i < inputs.size(); ++i) {
      RelNode child = inputs.get(i);
      if (!(child instanceof HepRelVertex)) {
        // Already replaced.
        continue;
      }
      child = buildFinalPlan((HepRelVertex) child);
      rel.replaceInput(i, child);
      rel.recomputeDigest();
    }

    return rel;
  }

  private void collectGarbage() {
    if (nTransformations == nTransformationsLastGC) {
      // No modifications have taken place since the last gc,
      // so there can't be any garbage.
      return;
    }
    nTransformationsLastGC = nTransformations;

    LOGGER.trace("collecting garbage");

    // Yer basic mark-and-sweep.
    final Set<HepRelVertex> rootSet = new HashSet<>();
    if (graph.vertexSet().contains(root)) {
      BreadthFirstIterator.reachable(rootSet, graph, root);
    }

    if (rootSet.size() == graph.vertexSet().size()) {
      // Everything is reachable:  no garbage to collect.
      return;
    }
    final Set<HepRelVertex> sweepSet = new HashSet<>();
    for (HepRelVertex vertex : graph.vertexSet()) {
      if (!rootSet.contains(vertex)) {
        sweepSet.add(vertex);
        RelNode rel = vertex.getCurrentRel();
        notifyDiscard(rel);
      }
    }
    assert !sweepSet.isEmpty();
    graph.removeAllVertices(sweepSet);
    graphSizeLastGC = graph.vertexSet().size();

    // Clean up digest map too.
    Iterator<Map.Entry<String, HepRelVertex>> digestIter =
        mapDigestToVertex.entrySet().iterator();
    while (digestIter.hasNext()) {
      HepRelVertex vertex = digestIter.next().getValue();
      if (sweepSet.contains(vertex)) {
        digestIter.remove();
      }
    }
  }

  private void assertNoCycles() {
    // Verify that the graph is acyclic.
    final CycleDetector<HepRelVertex, DefaultEdge> cycleDetector =
        new CycleDetector<>(graph);
    Set<HepRelVertex> cyclicVertices = cycleDetector.findCycles();
    if (cyclicVertices.isEmpty()) {
      return;
    }

    throw new AssertionError("Query graph cycle detected in HepPlanner: "
        + cyclicVertices);
  }

  //note: 仅仅是在 trace 日志中输出 Graph 信息
  private void dumpGraph() {
    if (!LOGGER.isTraceEnabled()) {
      return;
    }

    assertNoCycles();

    final RelMetadataQuery mq = root.getCluster().getMetadataQuery();
    final StringBuilder sb = new StringBuilder();
    sb.append("\nBreadth-first from root:  {\n");
    for (HepRelVertex vertex : BreadthFirstIterator.of(graph, root)) {
      sb.append("    ")
          .append(vertex)
          .append(" = ");
      RelNode rel = vertex.getCurrentRel();
      sb.append(rel)
          .append(", rowcount=")
          .append(mq.getRowCount(rel))
          .append(", cumulative cost=")
          .append(getCost(rel, mq))
          .append('\n');
    }
    sb.append("}");
    LOGGER.trace(sb.toString());
  }

  // implement RelOptPlanner
  public void registerMetadataProviders(List<RelMetadataProvider> list) {
    list.add(0, new HepRelMetadataProvider());
  }

  // implement RelOptPlanner
  public long getRelMetadataTimestamp(RelNode rel) {
    // TODO jvs 20-Apr-2006: This is overly conservative.  Better would be
    // to keep a timestamp per HepRelVertex, and update only affected
    // vertices and all ancestors on each transformation.
    return nTransformations;
  }

  @Override public ImmutableList<RelOptMaterialization> getMaterializations() {
    return ImmutableList.copyOf(materializations);
  }

  @Override public void addMaterialization(RelOptMaterialization materialization) {
    materializations.add(materialization);
  }
}

// End HepPlanner.java
