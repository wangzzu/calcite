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
package org.apache.calcite.rel.rules;

import org.apache.calcite.plan.RelOptRule;
import org.apache.calcite.plan.RelOptRuleCall;
import org.apache.calcite.plan.RelOptRuleOperand;
import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.EquiJoin;
import org.apache.calcite.rel.core.Filter;
import org.apache.calcite.rel.core.Join;
import org.apache.calcite.rel.core.JoinRelType;
import org.apache.calcite.rel.core.RelFactories;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rex.RexBuilder;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.rex.RexUtil;
import org.apache.calcite.tools.RelBuilder;
import org.apache.calcite.tools.RelBuilderFactory;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Sets;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Objects;

import static org.apache.calcite.plan.RelOptUtil.conjunctions;

/**
 * Planner rule that pushes filters above and
 * within a join node into the join node and/or its children nodes.
 */
public abstract class FilterJoinRule extends RelOptRule {
  /** Predicate that always returns true. With this predicate, every filter
   * will be pushed into the ON clause. */
  //note: 总是返回 true
  public static final Predicate TRUE_PREDICATE = (join, joinType, exp) -> true;

  /** Rule that pushes predicates from a Filter into the Join below them. */
  public static final FilterJoinRule FILTER_ON_JOIN =
      new FilterIntoJoinRule(true, RelFactories.LOGICAL_BUILDER,
          TRUE_PREDICATE);

  /** Dumber version of {@link #FILTER_ON_JOIN}. Not intended for production
   * use, but keeps some tests working for which {@code FILTER_ON_JOIN} is too
   * smart. */
  public static final FilterJoinRule DUMB_FILTER_ON_JOIN =
      new FilterIntoJoinRule(false, RelFactories.LOGICAL_BUILDER,
          TRUE_PREDICATE);

  /** Rule that pushes predicates in a Join into the inputs to the join. */
  public static final FilterJoinRule JOIN =
      new JoinConditionPushRule(RelFactories.LOGICAL_BUILDER, TRUE_PREDICATE);

  /** Whether to try to strengthen join-type. */
  private final boolean smart;

  /** Predicate that returns whether a filter is valid in the ON clause of a
   * join for this particular kind of join. If not, Calcite will push it back to
   * above the join. */
  private final Predicate predicate;

  //~ Constructors -----------------------------------------------------------

  /**
   * Creates a FilterProjectTransposeRule with an explicit root operand and
   * factories.
   */
  protected FilterJoinRule(RelOptRuleOperand operand, String id,
      boolean smart, RelBuilderFactory relBuilderFactory, Predicate predicate) {
    super(operand, relBuilderFactory, "FilterJoinRule:" + id);
    this.smart = smart;
    this.predicate = Objects.requireNonNull(predicate);
  }

  /**
   * Creates a FilterJoinRule with an explicit root operand and
   * factories.
   */
  @Deprecated // to be removed before 2.0
  protected FilterJoinRule(RelOptRuleOperand operand, String id,
      boolean smart, RelFactories.FilterFactory filterFactory,
      RelFactories.ProjectFactory projectFactory) {
    this(operand, id, smart, RelBuilder.proto(filterFactory, projectFactory),
        TRUE_PREDICATE);
  }

  /**
   * Creates a FilterProjectTransposeRule with an explicit root operand and
   * factories.
   */
  @Deprecated // to be removed before 2.0
  protected FilterJoinRule(RelOptRuleOperand operand, String id,
      boolean smart, RelFactories.FilterFactory filterFactory,
      RelFactories.ProjectFactory projectFactory,
      Predicate predicate) {
    this(operand, id, smart, RelBuilder.proto(filterFactory, projectFactory),
        predicate);
  }

  //~ Methods ----------------------------------------------------------------

  protected void perform(RelOptRuleCall call, Filter filter,
      Join join) {
    //note: 先拿到 join condition
    final List<RexNode> joinFilters =
        RelOptUtil.conjunctions(join.getCondition());
    final List<RexNode> origJoinFilters = ImmutableList.copyOf(joinFilters);

    // If there is only the joinRel,
    // make sure it does not match a cartesian product joinRel
    // (with "true" condition), otherwise this rule will be applied
    // again on the new cartesian product joinRel.
    if (filter == null && joinFilters.isEmpty()) {
      return;
    }

    //note: 拿到 filter 的 condition
    final List<RexNode> aboveFilters =
        filter != null
            ? conjunctions(filter.getCondition())
            : new ArrayList<>();
    final ImmutableList<RexNode> origAboveFilters =
        ImmutableList.copyOf(aboveFilters);

    // Simplify Outer Joins
    //note: 对 out join 做相应的转换（主要依据 condition 部分是否允许为 null 的情况，如果要求不能为 null，那么可以对其做相应的转化）
    //note: 比如 left join，并且要求左边表指定的值不能为 null，那么这个时候就可以转化为 inner 类型的 join
    JoinRelType joinType = join.getJoinType();
    if (smart
        && !origAboveFilters.isEmpty()
        && join.getJoinType() != JoinRelType.INNER) {
      joinType = RelOptUtil.simplifyJoin(join, origAboveFilters, joinType);
    }

    final List<RexNode> leftFilters = new ArrayList<>();
    final List<RexNode> rightFilters = new ArrayList<>();

    // TODO - add logic to derive additional filters.  E.g., from
    // (t1.a = 1 AND t2.a = 2) OR (t1.b = 3 AND t2.b = 4), you can
    // derive table filters:
    // (t1.a = 1 OR t1.b = 3)
    // (t2.a = 2 OR t2.b = 4)

    // Try to push down above filters. These are typically where clause
    // filters. They can be pushed down if they are not on the NULL
    // generating side.
    //note: 将 where 条件中的 filter 下推
    boolean filterPushed = false;
    if (RelOptUtil.classifyFilters(
        join,
        aboveFilters,
        joinType,
        !(join instanceof EquiJoin),
        !joinType.generatesNullsOnLeft(),
        !joinType.generatesNullsOnRight(),
        joinFilters,
        leftFilters,
        rightFilters)) {
      filterPushed = true;
    }

    // Move join filters up if needed
    validateJoinFilters(aboveFilters, joinFilters, join, joinType);

    // If no filter got pushed after validate, reset filterPushed flag
    if (leftFilters.isEmpty()
        && rightFilters.isEmpty()
        && joinFilters.size() == origJoinFilters.size()) {
      if (Sets.newHashSet(joinFilters)
          .equals(Sets.newHashSet(origJoinFilters))) {
        filterPushed = false;
      }
    }

    // Try to push down filters in ON clause. A ON clause filter can only be
    // pushed down if it does not affect the non-matching set, i.e. it is
    // not on the side which is preserved.
    //note: 将 on 条件中的 filter 下推
    if (RelOptUtil.classifyFilters(
        join,
        joinFilters,
        joinType,
        false,
        !joinType.generatesNullsOnRight(),
        !joinType.generatesNullsOnLeft(),
        joinFilters,
        leftFilters,
        rightFilters)) {
      filterPushed = true;
    }

    // if nothing actually got pushed and there is nothing leftover,
    // then this rule is a no-op
    //note: 如果什么都不需要做或者什么都没做
    if ((!filterPushed
            && joinType == join.getJoinType())
        || (joinFilters.isEmpty()
            && leftFilters.isEmpty()
            && rightFilters.isEmpty())) {
      return;
    }

    // create Filters on top of the children if any filters were
    // pushed to them
    //note: 根据 leftFilters 或 rightFilters 创建相应的 leftRel 和 rightRel
    final RexBuilder rexBuilder = join.getCluster().getRexBuilder();
    final RelBuilder relBuilder = call.builder();
    final RelNode leftRel =
        relBuilder.push(join.getLeft()).filter(leftFilters).build();
    final RelNode rightRel =
        relBuilder.push(join.getRight()).filter(rightFilters).build();

    // create the new join node referencing the new children and
    // containing its new join filters (if there are any)
    final ImmutableList<RelDataType> fieldTypes =
        ImmutableList.<RelDataType>builder()
            .addAll(RelOptUtil.getFieldTypeList(leftRel.getRowType()))
            .addAll(RelOptUtil.getFieldTypeList(rightRel.getRowType())).build();
    final RexNode joinFilter =
        RexUtil.composeConjunction(rexBuilder,
            RexUtil.fixUp(rexBuilder, joinFilters, fieldTypes));

    // If nothing actually got pushed and there is nothing leftover,
    // then this rule is a no-op
    if (joinFilter.isAlwaysTrue()
        && leftFilters.isEmpty()
        && rightFilters.isEmpty()
        && joinType == join.getJoinType()) {
      return;
    }

    //note: 创建一个新的 Join RelNode 节点
    RelNode newJoinRel =
        join.copy(
            join.getTraitSet(),
            joinFilter,
            leftRel,
            rightRel,
            joinType,
            join.isSemiJoinDone());
    call.getPlanner().onCopy(join, newJoinRel);
    if (!leftFilters.isEmpty()) {
      call.getPlanner().onCopy(filter, leftRel);
    }
    if (!rightFilters.isEmpty()) {
      call.getPlanner().onCopy(filter, rightRel);
    }

    relBuilder.push(newJoinRel);

    // Create a project on top of the join if some of the columns have become
    // NOT NULL due to the join-type getting stricter.
    relBuilder.convert(join.getRowType(), false);

    // create a FilterRel on top of the join if needed
    relBuilder.filter(
        RexUtil.fixUp(rexBuilder, aboveFilters,
            RelOptUtil.getFieldTypeList(relBuilder.peek().getRowType())));

    //note: 替换节点。此时会改变执行计划树，同时会触发新的Rule命中
    call.transformTo(relBuilder.build());
  }

  /**
   * Validates that target execution framework can satisfy join filters.
   *
   * <p>If the join filter cannot be satisfied (for example, if it is
   * {@code l.c1 > r.c2} and the join only supports equi-join), removes the
   * filter from {@code joinFilters} and adds it to {@code aboveFilters}.
   *
   * <p>The default implementation does nothing; i.e. the join can handle all
   * conditions.
   *
   * @param aboveFilters Filter above Join
   * @param joinFilters Filters in join condition
   * @param join Join
   * @param joinType JoinRelType could be different from type in Join due to
   * outer join simplification.
   */
  protected void validateJoinFilters(List<RexNode> aboveFilters,
      List<RexNode> joinFilters, Join join, JoinRelType joinType) {
    final Iterator<RexNode> filterIter = joinFilters.iterator();
    while (filterIter.hasNext()) {
      RexNode exp = filterIter.next();
      if (!predicate.apply(join, joinType, exp)) {
        aboveFilters.add(exp);
        filterIter.remove();
      }
    }
  }

  /** Rule that pushes parts of the join condition to its inputs. */
  public static class JoinConditionPushRule extends FilterJoinRule {
    public JoinConditionPushRule(RelBuilderFactory relBuilderFactory,
        Predicate predicate) {
      super(RelOptRule.operand(Join.class, RelOptRule.any()),
          "FilterJoinRule:no-filter", true, relBuilderFactory,
          predicate);
    }

    @Deprecated // to be removed before 2.0
    public JoinConditionPushRule(RelFactories.FilterFactory filterFactory,
        RelFactories.ProjectFactory projectFactory, Predicate predicate) {
      this(RelBuilder.proto(filterFactory, projectFactory), predicate);
    }

    @Override public void onMatch(RelOptRuleCall call) {
      Join join = call.rel(0);
      perform(call, null, join);
    }
  }

  /** Rule that tries to push filter expressions into a join
   * condition and into the inputs of the join. */
  //note: join and filter一起出现时可以进行相应的优化
  public static class FilterIntoJoinRule extends FilterJoinRule {
    public FilterIntoJoinRule(boolean smart,
        RelBuilderFactory relBuilderFactory, Predicate predicate) {
      super(
          operand(Filter.class,
              operand(Join.class, RelOptRule.any())),
          "FilterJoinRule:filter", smart, relBuilderFactory,
          predicate);
    }

    @Deprecated // to be removed before 2.0
    public FilterIntoJoinRule(boolean smart,
        RelFactories.FilterFactory filterFactory,
        RelFactories.ProjectFactory projectFactory,
        Predicate predicate) {
      this(smart, RelBuilder.proto(filterFactory, projectFactory), predicate);
    }

    @Override public void onMatch(RelOptRuleCall call) {
      Filter filter = call.rel(0);
      Join join = call.rel(1);
      perform(call, filter, join);
    }
  }

  /** Predicate that returns whether a filter is valid in the ON clause of a
   * join for this particular kind of join. If not, Calcite will push it back to
   * above the join. */
  public interface Predicate {
    boolean apply(Join join, JoinRelType joinType, RexNode exp);
  }
}

// End FilterJoinRule.java
