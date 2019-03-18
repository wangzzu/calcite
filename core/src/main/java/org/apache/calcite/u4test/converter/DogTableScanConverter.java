package org.apache.calcite.u4test.converter;
/*
 * Author: park.yq@alibaba-inc.com
 * Date: 2018/9/25 下午9:20
 */

import org.apache.calcite.adapter.enumerable.EnumerableConvention;
import org.apache.calcite.adapter.enumerable.EnumerableTableScan;
import org.apache.calcite.plan.RelOptRuleCall;
import org.apache.calcite.plan.RelTrait;
import org.apache.calcite.plan.RelTraitSet;
import org.apache.calcite.rel.RelDistributionTraitDef;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.convert.ConverterRule;
import org.apache.calcite.u4test.rel.DogRel;
import org.apache.calcite.u4test.rel.DogTableScan;

public class DogTableScanConverter extends ConverterRule {

    public static final DogTableScanConverter INSTANCE = new DogTableScanConverter(
        EnumerableTableScan.class, //note: experssion type
        EnumerableConvention.INSTANCE, //note: input convertion
        DogRel.CONVENTION, //note: converted convertion
        "DogTableScan"
    );

    @Override
    public boolean matches(RelOptRuleCall call) {
        return super.matches(call);
    }

    protected DogTableScanConverter(Class<? extends RelNode> clazz, RelTrait in, RelTrait out, String description) {
        super(clazz, in, out, description);
    }

    @Override
    //note: convert function
    public RelNode convert(RelNode rel) {
        EnumerableTableScan tableScan = (EnumerableTableScan)rel;
        return new DogTableScan(tableScan.getCluster(),
            RelTraitSet.createEmpty().plus(DogRel.CONVENTION).plus(RelDistributionTraitDef.INSTANCE.getDefault()),
            tableScan.getTable());
    }
}
