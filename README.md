# congruence_closure — 函数符号等式的同余闭包 + 布尔组合

离线、可复用、可产生证明的同余闭包（congruence closure）库，用于程序证明内核：
对无解释函数符号的等式理论做判定，并为每个推出的等式/矛盾给出可独立验证的证明。
在等式内核之上还提供一个布尔层：以等式/不等式为原子，支持与（AND）、或（OR）、
非（NOT）公式，原子数最多 8 个，通过真值表枚举并为每个候选赋值重建等式环境，
返回满足赋值或判定不可满足。

- Python 3.14.7，仅标准库，无任何第三方依赖，完全离线。
- 核心模块：`congruence_closure.py`（单文件，可直接 `import`）。
- 测试：`tests/test_congruence.py`（内核）、`tests/test_boolean.py`（布尔层）；演示：`demo.py`。

## 运行

```bash
python -m unittest discover -s tests -v
python demo.py
```

## 接口

### 等式内核

```python
from congruence_closure import CongruenceClosure, verify_proof, verify_contradiction

cc = CongruenceClosure(max_nodes=5000)   # max_nodes 可配，默认 5000
a  = cc.add_term("a")                    # 常量 = 零元函数应用，返回节点 id（int）
fa = cc.add_term("f", [a])               # 函数应用；结构相同的项被 hash-cons 到同一 id
cc.assert_equal(a, b)                    # 断言等式并做同余闭包；冲突抛 ContradictionError
cc.assert_distinct(a, b)                 # 断言不等；已相等则抛 ContradictionError
cc.apply_batch([("=", x, y), ("!=", z, w)])  # 批次断言，任一冲突则整批回滚
cc.are_equal(x, y)                       # 查询当前闭包中是否相等
proof = cc.explain(x, y)                 # 相等则返回证明，否则抛 NotEqualError
verify_proof(proof, x, y, cc.input_equalities, cc.terms)   # 独立验证，返回 True 或抛 ProofError
```

只读视图：`cc.terms`（节点 id → `(func, arg_ids)`）、`cc.input_equalities`、
`cc.distinct_assertions`、`cc.node_count`、`cc.max_nodes`、`cc.term_of(nid)`。
辅助：`term_to_str(nid, terms)`、`proof_to_str(proof, terms)` 用于打印。

### 布尔层（与/或/非 + 不等式入口）

```python
from congruence_closure import BooleanSolver, land, lor, lnot, MAX_BOOLEAN_ATOMS  # MAX_BOOLEAN_ATOMS == 8

sol = BooleanSolver(max_nodes=5000)      # 内部持有一个“模板”项 DAG
a, b, c = sol.add_term("a"), sol.add_term("b"), sol.add_term("c")
p = sol.add_atom(a, b)                   # 注册等式原子 a = b，返回原子下标（0 起）
q = sol.add_atom(b, c)                   # (a,b) 与 (b,a) 视为同一原子；最多 8 个
formula = land(lor(p, q), lnot(p))       # 公式：嵌套元组；原子直接用 int 下标
result = sol.solve(formula)              # 枚举；返回 SatResult
result.satisfiable                       # bool
result.assignment                        # 满足时为 (True, False, ...)，否则 None
sol.all_models(formula)                  # 全部满足赋值（元组）
model_cc = sol.build_environment(result.assignment)  # 按某个赋值重建内核，可继续 are_equal/explain
```

公式用普通嵌套元组表示（也可用辅助构造器）：

- 原子：非负 `int` 原子下标；
- `("not", p)`；
- `("and", p1, p2, ...)` / `("or", p1, p2, ...)`（至少一个子式）。

原子 `i` 为真表示注册的等式 `a_i = b_i` 成立，为假表示其“相反等式”——
不等式 `a_i != b_i`——成立。`solve` 对至多 2**8 = 256 个赋值做确定性枚举
（原子 0 为最低位，全假最先尝试）：先对公式做布尔求值，通过的候选在一个
**全新重建**的 `CongruenceClosure` 中把真原子断言为等式、假原子断言为
distinct；重建时按模板 DAG 顺序添加项，共享子项自然再次 hash-cons。候选闭包
相互独立且与求解器状态隔离，矛盾候选不留下任何部分状态，`solve` 可重复调用。
`build_environment(assignment)` 为指定赋值显式重建内核闭包；若该赋值本身与等式
理论矛盾（如假原子被同余强制相等），抛 `ContradictionError`。

### 证明格式

- 等式证明：边组成的链（tuple），每条边为
  - `("input", x, y)` —— 一条已断言的输入等式；
  - `("cong", t1, t2, (sub_i, ...))` —— 同余步：`t1 = f(u…)`、`t2 = f(v…)` 同函数符，
    `sub_i` 是第 i 个参数 `u_i = v_i` 的子证明（递归同构）。
- 矛盾证明：`("contradiction", eq_proof, (x, y))`，其中 `(x, y)` 是已断言的 distinct 对，
  `eq_proof` 推出 `x = y`。用 `verify_contradiction(proof, inputs, distincts, terms)` 验证。
- `ContradictionError` 自带完整证明包：`.proof`、`.inputs`、`.distincts`、`.terms`，
  回滚后仍可独立验证。

## 语义与契约

- **同余单向**：相同函数符、逐参数相等 ⇒ 结果相等；`f(a) = f(b)` **不**反推 `a = b`。
- **函数符元数固定**：首次使用即固定元数，之后元数不符抛 `ArityError`。
- **hash-consing**：结构相同的项共享同一节点 id（共享 DAG）。
- **原子性**：`assert_equal` / `assert_distinct` / `add_term` / `apply_batch` 均为原子操作；
  冲突时抛 `ContradictionError` 并回滚该操作（批次则回滚整批），不留部分变更。
- **错误语义**（均可定位到具体参数，不静默纠正）：
  - `ValidationError`：非法参数（节点 id 非 int、为 bool、为 float 含 NaN/Inf；
    函数符非非空字符串；批次 op 格式错误并标注下标；布尔公式节点不是原子下标或
    标注标签的元组、连接符非法、`not` 元数错、`and`/`or` 无子式、原子下标越界，
    错误消息带嵌套路径如 `solve: formula.and[1].not[0]` 等）。
  - `UnknownNodeError`：节点 id 越界。
  - `NodeLimitError`：共享 DAG 已达 `max_nodes`（默认 5000）上限。
  - `AtomLimitError`：布尔原子数超过 `MAX_BOOLEAN_ATOMS`（8）。
  - `NotEqualError`：`explain` 的两者不相等。算法是完备且终止的，这是确定性的
    “证明无解”，不是搜索预算耗尽；本模块唯一的资源上界是节点数上限
    （`NodeLimitError`），与“无解”严格区分。
  - `ContradictionError`：断言与已有 distinct 约束冲突，携带可验证证明。
    布尔层 `build_environment` 对自相矛盾的赋值也抛此异常（该路径无需证明链，
    `.proof` 为 `None`）。
  - `ProofError`：独立验证器拒绝证明，消息定位到失败步骤。
- **数值口径**：本模块不产生任何浮点结果，无误差容差问题；所有数值输入只接受
  `int`（拒绝 `bool`，拒绝 NaN/Infinity 等一切非 int 数值）。

## 设计取舍

- **算法**：Nelson–Oppen 式同余闭包。并查集（按大小合并 + 路径压缩）维护等价类；
  签名表 `(func, 参数代表元组) -> 节点` 在合并时只重算被合并类的父项签名，
  不做全项对比较；冲突检测用按类维护的 forbidden（distinct）表。
- **证明**：证明森林（proof forest）。每次合并记录一条边（输入等式或同余步），
  `explain` 在森林中找最近公共祖先取链，同余边递归展开参数子证明（带备忘）。
- **回滚**：每次变更操作前做状态快照（并查集、签名表、父表、forbidden 表、
  输入/不等列表等），失败时整体恢复。快照是该操作状态量的 O(n) 复制，
  换来实现的简单与回滚的绝对可靠；5000 节点上限下代价可忽略。
- **布尔层**：朴素真值表枚举（原子上界 8，最多 256 候选）。不对求解器或
  模板做任何断言；每个候选在新建的内核实例中按模板 DAG 顺序重建（同 id 顺序、
  共享子项重新 hash-cons），真原子断言等式、假原子断言 distinct（“相反等式”
  分支），矛盾即丢弃整个实例。分支隔离是结构性的（不依赖 undo/回滚），天然
  支持重复求解与 `find_all`；布尔求值与候选一致性检查相互独立。
- **递归深度**：`explain` / 验证器按项深度递归，必要时上调
  `sys.setrecursionlimit`（只升不降，界为 `4 * 节点数 + 100`）。

## 已知限制

- 只实现本题契约内的同余闭包（等式 + 无解释函数符 + distinct 约束），
  不含算术、数组等其他理论，也不做函数符单射性等额外推理；不宣称兼容任何
  SMT-LIB 等行业标准格式。
- 布尔层就是题面要求的枚举法：最多 8 个原子、256 行真值表，不做增量 SAT、
  学习子句、push/pop、unsat 核心或矛盾候选的等式证明链（矛盾候选直接判失败）；
  公式中的重复子式未做缓存，在 8 原子 / 256 候选尺度下无需优化。
- 证明规模最坏情形随输入等式数与项深度增长（链式证明未做长度压缩）。
- 快照式回滚在超大节点数下比增量 undo 日志更耗内存；在 5000 节点上限内无实际影响。
- 测试中的参考实现（`tests/test_congruence.py`、`tests/test_boolean.py` 内的
  全对暴力闭包 + 独立栈式公式求值器）独立于被测核心，仅用于小实例交叉验证。

## 文件

| 文件 | 说明 |
| --- | --- |
| `congruence_closure.py` | 核心库（等式内核 + 布尔层、证明、验证器、错误类型） |
| `tests/test_congruence.py` | 内核单元测试 + 独立参考闭包交叉验证 |
| `tests/test_boolean.py` | 布尔层测试：正常/边界/失败用例 + 独立参考全模型枚举交叉验证 |
| `demo.py` | 固定输入演示：正常证明、布尔求解、8 原子边界、批次/公式/赋值错误拒绝 |
