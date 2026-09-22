# congruence_closure — 函数符号等式的同余闭包

为离线程序证明内核提供的可复用模块：在共享 DAG 的基项（常量或固定元数函数应用）上维护等式的同余闭包，支持不等约束、冲突证明与批次回滚。

- **Python 版本**：3.14.7（Linux 原生运行）
- **依赖**：仅标准库，安装 Python 后无需安装任何其他依赖；核心、测试、演示全部离线
- **运行测试**：`python -m unittest discover -s tests -v`
- **运行演示**：`python demo.py`（确定性固定输入，真实计算，约 0.1 秒内完成）

## 接口

```python
from congruence_closure import CongruenceClosure, verify_proof

cc = CongruenceClosure(max_terms=5000, work_budget=1_000_000)

t  = cc.add_term("f", [a, b])   # 常量: cc.add_term("c")；哈希共享，相同结构返回同一 id
cc.assert_equal(a, b)           # 断言等式并做同余传播；返回是否发生合并
cc.assert_distinct(c, d)        # 断言不等约束
cc.assert_batch(equalities=[(x, y)], distincts=[(u, v)])  # 原子批次
cc.are_equal(a, b)              # -> bool
proof = cc.explain(a, b)        # -> 证明树（嵌套元组）
cc.term(t)                      # -> (symbol, (arg_id, ...))
cc.term_structure(t)            # -> 全结构形式 (symbol, (subterm, ...))
cc.input_equalities()           # -> 第 k 条输入等式的结构形式（证明叶子 ("input", k) 的所指）
cc.term_count / cc.class_count
```

### 证明格式与独立验证

`explain` 返回的证明树节点：`("input", k)`、`("cong", symbol, subs)`、`("trans", p, q)`、`("symm", p)`、`("refl", term)`。项的结构形式为 `(symbol, (subterm, ...))`，常量为 `(symbol, ())`。

`verify_proof(proof, input_equalities) -> (lhs, rhs)` 是**不依赖引擎**的独立校验器（`congruence_closure/proof.py` 不导入核心）：它只从证明树和输入等式列表重算出所证等式的两端。`ConflictError.proof` 与 `ConflictError.input_equalities` 在异常抛出时快照，批次回滚后仍可独立验证。

### 错误语义

所有错误继承 `CongruenceClosureError`：

| 异常 | 含义 |
|---|---|
| `InvalidInputError` | 非法输入（带 `param` 属性定位参数）。term id 必须为 `int`：拒绝 `bool`、非整数、NaN/Infinity、越界 id；symbol 必须为非空 `str`；同一 symbol 元数固定 |
| `LimitExceededError` | 共享 DAG 节点数达到 `max_terms`（默认 5000） |
| `BudgetExhaustedError` | 单次公开调用的传播步数预算耗尽（与"证明无解"严格区分），该调用已回滚 |
| `NotEqualError` | 对不相等的项调用 `explain`（证明无解） |
| `ConflictError` | 等式推出与 `assert_distinct` 矛盾；携带可独立验证的 `proof` |
| `InvalidProofError` | `verify_proof` 收到畸形或不成立的证明 |

**事务性**：`add_term` / `assert_equal` / `assert_distinct` / `assert_batch` 任一失败（冲突、预算、非法输入）都会把引擎回滚到调用前状态，不留部分变更。批次内任何元素失败则整批回滚。

## 输入上限

- `max_terms`：共享 DAG 节点数上限，默认 5000（题面接口边界；构造时可调）。
- `work_budget`：单次公开调用允许的合并 + 签名计算步数，默认 1 000 000；每次调用重置。

## 设计取舍

- **并查集按大小合并、不做路径压缩**：每次合并只写一条父指针，配合撤销日志（undo log）实现 O(1) 级单步回滚；`find` 代价为 O(log n)。
- **签名表 + 父指针重建**：签名 `(symbol, 各参数所在类代表)` → 项。合并后只重新登记被移动的较小类的成员的父项，不反复比较全部项对；表中陈旧条目在命中时重新校验同余性后覆盖。
- **证明森林**：每次合并在被合并的两项间加一条带来源（输入等式编号或同余边）的边，森林中路径唯一；`explain` 沿路径生成证明树，同余边递归解释逐参数相等。
- **不可反推**：同余只从参数相等推向结果相等；`f(a)=f(b)` 不会推出 `a=b`（有测试与参考实现双重覆盖）。
- **explain 会临时提高递归限制**（项 DAG 可能很深），用上下文管理器恢复原值。

## 已知限制

- 仅处理基项（无变量、无 AC 符号、无量词），按本题契约实现，不宣称完整 SMT/定理证明器兼容。
- 无路径压缩，单次 `find` 为 O(log n)；`explain` 的证明规模最坏可达合并链长度量级。
- 单线程、纯内存；不提供序列化持久化。
- **误差口径**：本模块不输出任何浮点结果，等式判定为精确布尔值，证明验证为精确结构相等，无浮点误差问题。

## 目录

- `congruence_closure/core.py` — 引擎与错误类型
- `congruence_closure/proof.py` — 独立证明校验器（不导入核心）
- `tests/test_congruence_closure.py` — 单元测试 + 枚举等价闭包的独立参考实现对照
- `demo.py` — 固定输入演示：正常结果、不可反推、批次冲突回滚、非法输入拒绝
