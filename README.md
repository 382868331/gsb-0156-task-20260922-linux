# congruence_closure — 函数符号等式的同余闭包

离线、可复用、可产生证明的同余闭包（congruence closure）库，用于程序证明内核：
对无解释函数符号的等式理论做判定，并为每个推出的等式/矛盾给出可独立验证的证明。
函数符号可选声明为**单射（injective）**：已声明单射的函数两次应用相等时，
逐位置反推参数相等，并可与正向同余连锁触发；未声明的函数仍只做单向同余。

- Python 3.14.7，仅标准库，无任何第三方依赖，完全离线。
- 核心模块：`congruence_closure.py`（单文件，可直接 `import`）。
- 测试：`tests/test_congruence.py`、`tests/test_injective.py`；
  演示：`demo.py`（基础同余）、`demo_iteration.py`（单射迭代）。

## 环境准备

需要 Linux 原生 Python 3.14.7，仅标准库，无需安装任何第三方包；建议用 venv 隔离：

```bash
python3.14 -m venv .venv        # 仓库内 .venv 已按此准备
.venv/bin/python --version      # 应显示 Python 3.14.7
```

## 运行

```bash
python -m unittest discover -s tests -v
python demo.py
python demo_iteration.py
```

测试与演示均离线、确定性、无 sleep；`demo_iteration.py` 真实计算正常与
边界结果，运行时间远低于 90 秒。

## 接口

```python
from congruence_closure import CongruenceClosure, verify_proof, verify_contradiction

cc = CongruenceClosure(max_nodes=5000)   # max_nodes 可配，默认 5000
a  = cc.add_term("a")                    # 常量 = 零元函数应用，返回节点 id（int）
fa = cc.add_term("f", [a])               # 函数应用；结构相同的项被 hash-cons 到同一 id
cc.assert_equal(a, b)                    # 断言等式并做同余闭包；冲突抛 ContradictionError
cc.assert_distinct(a, b)                 # 断言不等；已相等则抛 ContradictionError
cc.apply_batch([("=", x, y), ("!=", z, w)])  # 批次断言，任一冲突则整批回滚
cc.declare_injective("f")                # 声明函数符 f 单射；幂等，可回溯生效
cc.are_equal(x, y)                       # 查询当前闭包中是否相等
proof = cc.explain(x, y)                 # 相等则返回证明，否则抛 NotEqualError
verify_proof(proof, x, y, cc.input_equalities, cc.terms, cc.injective_functions)
                                         # 独立验证，返回 True 或抛 ProofError
```

只读视图：`cc.terms`（节点 id → `(func, arg_ids)`）、`cc.input_equalities`、
`cc.distinct_assertions`、`cc.injective_functions`、`cc.node_count`、
`cc.max_nodes`、`cc.term_of(nid)`。
辅助：`term_to_str(nid, terms)`、`proof_to_str(proof, terms)` 用于打印。

### 证明格式

- 等式证明：边组成的链（tuple），每条边为
  - `("input", x, y)` —— 一条已断言的输入等式；
  - `("cong", t1, t2, (sub_i, ...))` —— 同余步：`t1 = f(u…)`、`t2 = f(v…)` 同函数符，
    `sub_i` 是第 i 个参数 `u_i = v_i` 的子证明（递归同构）。
  - `("inj", t1, t2, k, premise)` —— 单射步：`t1`、`t2` 是同一个已声明单射函数符
    的应用，`premise` 是 `t1 = t2` 的子证明，本步推出第 k 个参数相等。
- 矛盾证明：`("contradiction", eq_proof, (x, y))`，其中 `(x, y)` 是已断言的 distinct 对，
  `eq_proof` 推出 `x = y`。用
  `verify_contradiction(proof, inputs, distincts, terms, injective)` 验证。
- `ContradictionError` 自带完整证明包：`.proof`、`.inputs`、`.distincts`、`.terms`、
  `.injective`，回滚后仍可独立验证。验证器只逐步重放证明，不接触并查集分组。

## 语义与契约

- **同余单向**：相同函数符、逐参数相等 ⇒ 结果相等。
- **单射可选**：仅对 `declare_injective` 声明过的函数符，`f(u…) = f(v…)` 逐位置
  反推 `u_i = v_i`；未声明的函数符绝不反推。反向传播与正向同余共用同一工作
  队列，只在等价类真正合并时推进，有限项上必然收敛，不反复制造相同等式。
- **声明可回溯**：`declare_injective` 对已有项立即生效；若回溯合并与 distinct
  冲突，则抛 `ContradictionError` 并整体回滚该声明。
- **只推理已有项**：不生成新的函数应用，不引入满射或“不同函数像不相交”等假设。
- **函数符元数固定**：首次使用即固定元数，之后元数不符抛 `ArityError`。
- **hash-consing**：结构相同的项共享同一节点 id（共享 DAG）。
- **原子性**：`assert_equal` / `assert_distinct` / `add_term` / `apply_batch` 均为原子操作；
  冲突时抛 `ContradictionError` 并回滚该操作（批次则回滚整批），不留部分变更。
- **错误语义**（均可定位到具体参数，不静默纠正）：
  - `ValidationError`：非法参数（节点 id 非 int、为 bool、为 float 含 NaN/Inf；
    函数符非非空字符串；批次 op 格式错误并标注下标等）。
  - `UnknownNodeError`：节点 id 越界。
  - `NodeLimitError`：共享 DAG 已达 `max_nodes`（默认 5000）上限。
  - `NotEqualError`：`explain` 的两者不相等。算法是完备且终止的，这是确定性的
    “证明无解”，不是搜索预算耗尽；本模块唯一的资源上界是节点数上限
    （`NodeLimitError`），与“无解”严格区分。
  - `ContradictionError`：断言与已有 distinct 约束冲突，携带可验证证明。
  - `ProofError`：独立验证器拒绝证明，消息定位到失败步骤。
- **数值口径**：本模块不产生任何浮点结果，无误差容差问题；所有数值输入只接受
  `int`（拒绝 `bool`，拒绝 NaN/Infinity 等一切非 int 数值）。

## 设计取舍

- **算法**：Nelson–Oppen 式同余闭包。并查集（按大小合并 + 路径压缩）维护等价类；
  签名表 `(func, 参数代表元组) -> 节点` 在合并时只重算被合并类的父项签名，
  不做全项对比较；冲突检测用按类维护的 forbidden（distinct）表。
- **单射**：每个等价类维护 `单射函数符 -> 该类中一个应用节点` 的表；两类合并时，
  同一单射函数符在两侧都有应用即把对应参数对推入合并队列（理由为 inj 步），
  与正向同余在同一工作队列中连锁收敛。
- **证明**：证明森林（proof forest）。每次合并记录一条边（输入等式或同余步），
  `explain` 在森林中找最近公共祖先取链，同余边递归展开参数子证明（带备忘）。
  单射边额外携带 `t1 = t2` 的前提子证明，使证书自包含、可逐步重放。
- **回滚**：每次变更操作前做状态快照（并查集、签名表、父表、forbidden 表、
  输入/不等列表等），失败时整体恢复。快照是该操作状态量的 O(n) 复制，
  换来实现的简单与回滚的绝对可靠；5000 节点上限下代价可忽略。
- **递归深度**：`explain` / 验证器按项深度递归，必要时上调
  `sys.setrecursionlimit`（只升不降，界为 `4 * 节点数 + 100`）。

## 已知限制

- 只实现本题契约内的同余闭包（等式 + 无解释函数符 + distinct 约束 + 可选单射
  声明），不含算术、数组等其他理论，不做满射或像集不相交等额外推理；
  不宣称兼容任何 SMT-LIB 等行业标准格式。
- 证明规模最坏情形随输入等式数与项深度增长（链式证明未做长度压缩）。
- 快照式回滚在超大节点数下比增量 undo 日志更耗内存；在 5000 节点上限内无实际影响。
- 测试中的参考实现（`tests/test_congruence.py`、`tests/test_injective.py` 内的
  全对暴力闭包）独立于被测核心，仅用于小实例交叉验证（含可满足性对照）。

## 文件

| 文件 | 说明 |
| --- | --- |
| `congruence_closure.py` | 核心库（数据结构、证明、验证器、错误类型） |
| `tests/test_congruence.py` | 单元测试 + 独立参考闭包交叉验证（基础同余） |
| `tests/test_injective.py` | 单射行为测试 + 独立参考闭包交叉验证（含可满足性） |
| `demo.py` | 固定输入演示：正常证明、批次冲突回滚、非法输入拒绝 |
| `demo_iteration.py` | 单射演示：嵌套反推、二元参数互换、与不等式冲突 |
