package org.apache.calcite.u4test;

import org.apache.calcite.adapter.enumerable.EnumerableConvention;
import org.apache.calcite.config.CalciteConnectionConfig;
import org.apache.calcite.config.CalciteConnectionConfigImpl;
import org.apache.calcite.jdbc.CalciteSchema;
import org.apache.calcite.plan.Context;
import org.apache.calcite.plan.ConventionTraitDef;
import org.apache.calcite.plan.RelOptCluster;
import org.apache.calcite.plan.RelOptPlanner;
import org.apache.calcite.plan.RelOptTable;
import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.plan.RelTraitSet;
import org.apache.calcite.plan.volcano.VolcanoPlanner;
import org.apache.calcite.prepare.CalciteCatalogReader;
import org.apache.calcite.rel.RelDistributionTraitDef;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.RelRoot;
import org.apache.calcite.rel.rules.FilterJoinRule;
import org.apache.calcite.rel.rules.PruneEmptyRules;
import org.apache.calcite.rel.rules.ReduceExpressionsRule;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rel.type.RelDataTypeFactory;
import org.apache.calcite.rel.type.RelDataTypeSystem;
import org.apache.calcite.rel.type.RelDataTypeSystemImpl;
import org.apache.calcite.rex.RexBuilder;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.schema.impl.AbstractTable;
import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.SqlOperatorTable;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.sql.parser.SqlParser;
import org.apache.calcite.sql.type.BasicSqlType;
import org.apache.calcite.sql.type.SqlTypeFactoryImpl;
import org.apache.calcite.sql.type.SqlTypeName;
import org.apache.calcite.sql.util.ChainedSqlOperatorTable;
import org.apache.calcite.sql.validate.SqlConformance;
import org.apache.calcite.sql.validate.SqlConformanceEnum;
import org.apache.calcite.sql.validate.SqlValidator;
import org.apache.calcite.sql.validate.SqlValidatorUtil;
import org.apache.calcite.sql2rel.RelDecorrelator;
import org.apache.calcite.sql2rel.SqlToRelConverter;
import org.apache.calcite.sql2rel.StandardConvertletTable;
import org.apache.calcite.tools.FrameworkConfig;
import org.apache.calcite.tools.Frameworks;
import org.apache.calcite.tools.RelBuilder;

import java.util.List;
import java.util.Properties;

/**
 * 一个测试程序，方便源码追查
 *
 * @author matt
 * @date 2019-03-03 14:22
 */
public class MattTest {
    public static void main(String[] args) {
        try {
            //note: 初始化一个SchemaPlus实例，可以添加table、子schema等
            SchemaPlus rootSchema = Frameworks.createRootSchema(true);
            //note: add a table
            rootSchema.add("USERS", new AbstractTable() {
                @Override
                public RelDataType getRowType(final RelDataTypeFactory typeFactory) {
                    RelDataTypeFactory.Builder builder = typeFactory.builder();

                    builder.add("ID", new BasicSqlType(new RelDataTypeSystemImpl() {}, SqlTypeName.INTEGER));
                    builder.add("NAME", new BasicSqlType(new RelDataTypeSystemImpl() {}, SqlTypeName.CHAR));
                    builder.add("TIME_D", new BasicSqlType(new RelDataTypeSystemImpl() {}, SqlTypeName.DATE));
                    return builder.build();
                }
            });

            rootSchema.add("SCORE", new AbstractTable() {
                @Override
                public RelDataType getRowType(final RelDataTypeFactory typeFactory) {
                    RelDataTypeFactory.Builder builder = typeFactory.builder();

                    builder.add("ID", new BasicSqlType(new RelDataTypeSystemImpl() {}, SqlTypeName.INTEGER));
                    builder.add("SCORE", new BasicSqlType(new RelDataTypeSystemImpl() {}, SqlTypeName.INTEGER));
                    return builder.build();
                }
            });

            //note: 可以table内部类中定义getStatistic()等方法
            rootSchema.add("TABLE_RESULT", new AbstractTable() {
                @Override
                public RelDataType getRowType(final RelDataTypeFactory typeFactory) {
                    RelDataTypeFactory.Builder builder = typeFactory.builder();

                    builder.add("ID", new BasicSqlType(new RelDataTypeSystemImpl() {}, SqlTypeName.INTEGER));
                    builder.add("NAME", new BasicSqlType(new RelDataTypeSystemImpl() {}, SqlTypeName.CHAR));
                    builder.add("SCORE", new BasicSqlType(new RelDataTypeSystemImpl() {}, SqlTypeName.INTEGER));
                    return builder.build();
                }
            });

            rootSchema.add("FINAL_RESULT", new AbstractTable() {
                public RelDataType getRowType(final RelDataTypeFactory typeFactory) {
                    RelDataTypeFactory.Builder builder = typeFactory.builder();

                    builder.add("ID", new BasicSqlType(new RelDataTypeSystemImpl() {}, SqlTypeName.INTEGER));
                    builder.add("SOURCE_DS", new BasicSqlType(new RelDataTypeSystemImpl() {}, SqlTypeName.VARCHAR));
                    builder.add("DS", new BasicSqlType(new RelDataTypeSystemImpl() {}, SqlTypeName.VARCHAR));
                    return builder.build();
                }
            });

            rootSchema.add("MY_SOURCE", new AbstractTable() {
                public RelDataType getRowType(final RelDataTypeFactory typeFactory) {
                    RelDataTypeFactory.Builder builder = typeFactory.builder();

                    builder.add("ID", new BasicSqlType(new RelDataTypeSystemImpl() {}, SqlTypeName.INTEGER));
                    builder.add("SOURCE_DS", new BasicSqlType(new RelDataTypeSystemImpl() {}, SqlTypeName.VARCHAR));
                    builder.add("DS", new BasicSqlType(new RelDataTypeSystemImpl() {}, SqlTypeName.VARCHAR));
                    return builder.build();
                }
            });

            //note: 通过 Frameworks tools 做相应的配置
            final FrameworkConfig config = Frameworks.newConfigBuilder()
                .parserConfig(SqlParser.Config.DEFAULT) //note: 设置 SQL parser 的配置
                .defaultSchema(rootSchema) //note：设置相应的schema和table信息
                .traitDefs(ConventionTraitDef.INSTANCE, RelDistributionTraitDef.INSTANCE)
                .build();
            String sql
                = "select time_d from users where id > 100 or id > 400 and id in (select id from users where id < 500)";
            //note: sql to RelNode
            //String sql = "insert into final_result select id, cast(1 as varchar) as ds, ds as source_ds from
            // my_source";

            //note: optimize sql
            //HepProgramBuilder builder = new HepProgramBuilder();
            //builder.addRuleInstance(FilterJoinRule.FilterIntoJoinRule.FILTER_ON_JOIN); //note: 添加 rule
            //HepPlanner hepPlanner = new HepPlanner(builder.build());
            //hepPlanner.setRoot(relNode);
            //relNode = hepPlanner.findBestExp();

            //note: 2. 使用 VolcanoPlanner
            VolcanoPlanner planner = new VolcanoPlanner();
            planner.addRelTraitDef(ConventionTraitDef.INSTANCE);
            planner.addRelTraitDef(RelDistributionTraitDef.INSTANCE);
            planner.addRule(FilterJoinRule.FilterIntoJoinRule.FILTER_ON_JOIN);
            planner.addRule(ReduceExpressionsRule.PROJECT_INSTANCE);
            planner.addRule(PruneEmptyRules.PROJECT_INSTANCE);

            RelNode relNode = sqlToRelNode(rootSchema, config, sql, planner);

            RelTraitSet desiredTraits =
                relNode.getCluster().traitSet().replace(EnumerableConvention.INSTANCE);
            relNode = planner.changeTraits(relNode, desiredTraits);

            planner.setRoot(relNode);
            relNode = planner.findBestExp();

            System.out.println("-----------------------------------------------------------");
            System.out.println("The Best relational expression string:");
            System.out.println(RelOptUtil.toString(relNode));
            System.out.println("-----------------------------------------------------------");
            //note: 上面是一个完整的流程：sql --> SqlNode --> RelNode --> Hep-Planner

        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    public static RelNode sqlToRelNode(SchemaPlus rootScheme, FrameworkConfig frameworkConfig, String sql,
                                       RelOptPlanner planner) {
        try {
            /**
             * note: 一、sql parser(初始化SqlParser实例，然后做相应的解析)
             */
            SqlParser parser = SqlParser.create(sql, SqlParser.Config.DEFAULT);
            System.out.println("SqlParser:");
            System.out.println(parser.toString());
            System.out.println("--------------------------------------------------------\n");
            SqlNode sqlNode = parser.parseStmt();
            System.out.println("SqlNode:");
            System.out.println(sqlNode.toString());
            System.out.println("-----------------------------------\n");

            //note: 二、sql validate（会先通过Catalog读取获取相应的metadata和namespace）
            //note: get metadata and namespace
            SqlTypeFactoryImpl factory = new SqlTypeFactoryImpl(RelDataTypeSystem.DEFAULT);
            CalciteCatalogReader calciteCatalogReader = new CalciteCatalogReader(
                CalciteSchema.from(rootScheme),
                CalciteSchema.from(rootScheme).path(null), //note:对于rootSchema这里没有parent
                factory,
                new CalciteConnectionConfigImpl(new Properties()));

            //note: 校验（包括对表名，字段名，函数名，数据类型的校验。）
            SqlValidator validator = SqlValidatorUtil.newValidator(SqlStdOperatorTable.instance(), calciteCatalogReader,
                factory,
                conformance(frameworkConfig));
            SqlNode validateSqlNode = validator.validate(sqlNode);

            //note：to supported user' define function
            SqlOperatorTable sqlOperatorTable = ChainedSqlOperatorTable.of(frameworkConfig.getOperatorTable(),
                calciteCatalogReader);

            /**
             * note: 三、convert SqlNode --> RelNode
             */
            //note: 1. init the rexBuilder
            final RexBuilder rexBuilder = new RexBuilder(factory);

            //note: 3. cluster: An environment for related relational expressions during the optimization of a query.
            final RelOptCluster cluster = RelOptCluster.create(planner, rexBuilder);

            //note: 4. init SqlToRelConverter
            final SqlToRelConverter.Config config = SqlToRelConverter.configBuilder()
                .withConfig(frameworkConfig.getSqlToRelConverterConfig())
                .withTrimUnusedFields(false)
                .withConvertTableAccess(false)
                .build(); //note: config
            final SqlToRelConverter sqlToRelConverter = new SqlToRelConverter(new DogView(), validator,
                calciteCatalogReader, cluster, StandardConvertletTable.INSTANCE, config);

            //note: 5. convert to RelNode
            RelRoot root = sqlToRelConverter.convertQuery(validateSqlNode, false, true);

            root = root.withRel(sqlToRelConverter.flattenTypes(root.rel, true));
            final RelBuilder relBuilder = config.getRelBuilderFactory().create(cluster, null);
            root = root.withRel(RelDecorrelator.decorrelateQuery(root.rel, relBuilder));

            RelNode relNode = root.rel;
            return root.rel;

        } catch (Exception e) {
            e.printStackTrace();
        }

        return null;
    }

    private static class DogView implements RelOptTable.ViewExpander {
        public DogView() {
        }

        @Override
        public RelRoot expandView(RelDataType rowType, String queryString, List<String> schemaPath,
                                  List<String> viewPath) {
            return null;
        }
    }

    private static RexBuilder createRexBuilder(RelDataTypeFactory typeFactory) {
        return new RexBuilder(typeFactory);
    }

    /**
     * note: 找到 RootSchema，一直向着parent节点去查找
     *
     * @param schema
     * @return
     */
    private static SchemaPlus rootSchema(SchemaPlus schema) {
        for (; ; ) {
            if (schema.getParentSchema() == null) {
                return schema;
            }
            schema = schema.getParentSchema();
        }
    }

    private static SqlConformance conformance(FrameworkConfig config) {
        final Context context = config.getContext();
        if (context != null) {
            final CalciteConnectionConfig connectionConfig =
                context.unwrap(CalciteConnectionConfig.class);
            if (connectionConfig != null) {
                return connectionConfig.conformance();
            }
        }
        return SqlConformanceEnum.DEFAULT;
    }
}
