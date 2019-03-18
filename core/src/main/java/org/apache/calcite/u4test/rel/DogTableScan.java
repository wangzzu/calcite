package org.apache.calcite.u4test.rel;/*
 * Author: park.yq@alibaba-inc.com
 * Date: 2018/9/30 下午2:27
 */

import org.apache.calcite.plan.RelOptCluster;
import org.apache.calcite.plan.RelOptCost;
import org.apache.calcite.plan.RelOptPlanner;
import org.apache.calcite.plan.RelOptTable;
import org.apache.calcite.plan.RelTraitSet;
import org.apache.calcite.rel.core.TableScan;
import org.apache.calcite.rel.metadata.RelMetadataQuery;
import org.apache.calcite.u4test.cost.DogRelMetadataQuery;

public class DogTableScan extends TableScan implements DogRel {
    public DogTableScan(RelOptCluster cluster, RelTraitSet traitSet, RelOptTable table) {
        super(cluster, traitSet, table);
    }

    @Override
    public RelOptCost computeSelfCost(RelOptPlanner planner, RelMetadataQuery mq) {
        //return super.computeSelfCost(planner, mq);
        return DogRelMetadataQuery.INSTNACE.getCumulativeCost(this);
    }
}
