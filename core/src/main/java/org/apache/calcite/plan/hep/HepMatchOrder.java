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

/**
 * HepMatchOrder specifies the order of graph traversal when looking for rule
 * matches.
 */
public enum HepMatchOrder {
  /**
   * Match in arbitrary order. This is the default because it is
   * efficient, and most rules don't care about order.
   * note：按任意顺序匹配，默认设置（因为它是有效的，而且大部分的 rule 并不关心顺序）
   */
  ARBITRARY,

  /**
   * Match from leaves up. A match attempt at a descendant precedes all match
   * attempts at its ancestors.
   * note：自下而上，先从子节点开始匹配
   */
  BOTTOM_UP,

  /**
   * Match from root down. A match attempt at an ancestor always precedes all
   * match attempts at its descendants.
   * note：自上而下，先从父节点开始匹配
   */
  TOP_DOWN,

  /**
   * Match in depth-first order.
   * note：深度优先匹配，某些情况下比 ARBITRARY 高效（为了避免新的 vertex 产生后又从 root 开始匹配）
   *
   * <p>It avoids applying a rule to the previous
   * {@link org.apache.calcite.rel.RelNode} repeatedly after new vertex is
   * generated in one rule application. It can therefore be more efficient than
   * {@link #ARBITRARY} in cases such as
   * {@link org.apache.calcite.rel.core.Union} with large fan-out.
   */
  DEPTH_FIRST
}

// End HepMatchOrder.java
