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
package org.apache.calcite.adapter.csv;

import org.apache.calcite.adapter.java.JavaTypeFactory;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rel.type.RelDataTypeFactory;
import org.apache.calcite.rel.type.RelProtoDataType;
import org.apache.calcite.schema.impl.AbstractTable;
import org.apache.calcite.util.Source;

import java.util.ArrayList;
import java.util.List;

/**
 * Base class for table that reads CSV files.
 */
public abstract class CsvTable extends AbstractTable {
  protected final Source source;
  protected final RelProtoDataType protoRowType;
  protected List<CsvFieldType> fieldTypes;

  /** Creates a CsvTable. */
  CsvTable(Source source, RelProtoDataType protoRowType) {
    this.source = source;
    this.protoRowType = protoRowType;
  }

  //note: table定义的虚方法，定义table行记录的字段及字段类型
  public RelDataType getRowType(RelDataTypeFactory typeFactory) {
    if (protoRowType != null) {
      return protoRowType.apply(typeFactory);
    }
    if (fieldTypes == null) {
      fieldTypes = new ArrayList<>();
      return CsvEnumerator.deduceRowType((JavaTypeFactory) typeFactory, source,
          fieldTypes);
    } else {
      return CsvEnumerator.deduceRowType((JavaTypeFactory) typeFactory, source,
          null);
    }
  }

  /** Various degrees of table "intelligence". note：不同的类型，涉及到优化器相关 */
  public enum Flavor {
    SCANNABLE, FILTERABLE, TRANSLATABLE
  }
}

// End CsvTable.java
