# congruence_closure — 函数符号等式的同余闭包（含可选单射声明）

离线、可复用、可产生证明的同余闭包（congruence closure）库，用于程序证明内核：
对无解释函数符号的等式理论做判定，并为每个推出的等式/矛盾给出可独立验证的证明。

- Python 3.14.7（Linux 原生），仅标准库，无任何第三方依赖，完全离线。
- 核心模块：`congruence_closure.py`（单文件，可直接 `import`）。
- 测试：`tests/test_congruence.py`；演示：`demo.py` 与 `demo_iteration.py`。
- 函数符号可选用 `declare_injective` 声明为单射：同一单射函数两次应用结果相等时，
  逐位置推出参数相等；未声明的函数仍只做原来的正向同余推理。

## 运行

```bash
python3.14 -m venv .venv
source .venv/bin/activate          # 可选；仅标准库，不激活也可直接用系统 python3.14
python -m pip install -r requirements.txt   # 本项目无第三方依赖，通常为空操作
python -m unittest discover -s tests -v
python demo.py
python demo_iteration.py
```

测试与两个演示均为确定性实时计算，不含 `sleep`、网络、Docker、外部服务或真实凭据。
`demo_iteration.py` 在普通机器上耗时远低于 90 秒（实测约 0.02 秒）。

## 接口

```python
from congruence_closure import CongruenceClosure, verify_proof, verify_contradiction

cc = CongruenceClosure(max_nodes=5000)   # max_nodes 可配，默认 5000
a  = cc.add_term("a")                    # 常量 = 零元函数应用，返回节点 id（int）
fa = cc.add_term("f", [a])               # 函数应用；结构相同的项被 hash-cons 到同一 id
cc.declare_injective("f")                # 声明函数符号单射（幂等，可早于首次使用）
cc.assert_equal(a, b)                    # 断言等式并做闭包；冲突抛 ContradictionError
cc.assert_distinct(a, b)                 # 断言不等；已相等则抛 ContradictionError
cc.apply_batch([("=", x, y), ("!=", z, w)])  # 批次断言，任一冲突则整批回滚
cc.are_equal(x, y)                       # 查询当前闭包中是否相等
proof = cc.explain(x, y)                 # 相等则返回证明，否则抛 NotEqualError
verify_proof(proof, x, y, cc.input_equalities, cc.terms,
             cc.injective_symbols)       # 独立验证，返回 True 或抛 ProofError
verify_contradiction(err.proof, err.inputs, err.distincts,
                     err.terms, err.injectives)
```

只读视图：`cc.terms`（节点 id → `(func, arg_ids)`）、`cc.input_equalities`、
`cc.distinct_assertions`、`cc.injective_symbols`、`cc.node_count`、
`cc.max_nodes`、`cc.term_of(nid)`。
辅助：`term_to_str(nid, terms)`、`proof_to_str(proof, terms)` 用于打印。

### 证明格式

- 等式证明：边组成的链（tuple），每条边为
  - `("input", x, y)` —— 一条已断言的输入等式；
  - `("cong", t1, t2, (sub_i, ...))` —— 正向同余步：`t1 = f(u…)`、
    `t2 = f(v…)` 同函数符，`sub_i` 是第 i 个参数 `u_i = v_i` 的子证明；
  - `("inject", t1, t2, k, output_proof)` —— 单射步：`t1`、`t2` 是同一
    **已声明单射**函数的两个应用，`output_proof` 独立重放出 `t1 = t2`，
    由此推出第 k 个位置的参数相等。
- 矛盾证明：`("contradiction", eq_proof, (x, y))`，其中 `(x, y)` 是已断言的
  distinct 对，`eq_proof` 推出 `x = y`。用
  `verify_contradiction(proof, inputs, distincts, terms, injectives)` 验证。
- `ContradictionError` 自带完整证明包：`.proof`、`.inputs`、`.distincts`、
  `.injectives`、`.terms`，回滚后仍可独立验证。
- 独立检查器逐步重放每条链：它只接受真正在 `inputs` 中的输入等式，只在
  `injectives` 声明集里使用单射步，并递归验证全部子证明；它不读取并查集
  的最终分组。

## 语义与契约

- **同余默认为单向**：相同函数符、逐参数相等 ⇒ 结果相等。
  `f(a) = f(b)` 在 `f` 未声明单射时**不**反推 `a = b`。
- **单射为可选声明**：对已声明单射的 `f`，`f(u₁,…,uₙ) = f(v₁,…,vₙ)` 逐位置
  推出 `u_i = v_i`。只在已存在的有限项之间推理，**不**生成新的函数应用；
  声明在等式之前或之后给出都会对当时已有的项立即闭合。
- **不做额外假设**：不引入满射；不同函数符号的像**不**假定不相交
  （`f(a) = g(b)` 既不反推参数，也不制造冲突）。
- **连锁收敛**：正向同余与反向单射都进入同一个工作队列；只有真正合并两个
  不同等价类时才记录一条证明边并入队传播，等价的类直接跳过，因此不会反复
  制造相同等式，队列在有限项上必收敛。
- **函数符元数固定**：首次使用即固定元数，之后元数不符抛 `ArityError`。
- **hash-consing**：结构相同的项共享同一节点 id（共享 DAG）。
- **原子性**：`assert_equal` / `assert_distinct` / `declare_injective` /
  `add_term` / `apply_batch` 均为原子操作；冲突时抛 `ContradictionError` 并
  回滚该操作（批次则回滚整批），不留部分变更。
- **错误语义**（均可定位到具体参数，不静默纠正）：
  - `ValidationError`：非法参数（节点 id 非 int、为 bool、为 float 含
    NaN/Inf；函数符非非空字符串；批次 op 格式错误并标注下标等）。
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

- **算法**：Nelson–Oppen 式同余闭包。并查集（按大小合并 + 路径压缩）维护
  等价类；签名表 `(func, 参数代表元组) -> 节点` 在合并时只重算被合并类的父项
  签名，不做全项对比较；冲突检测用按类维护的 forbidden（distinct）表。
- **单射索引**：另按等价类维护 `{单射函数符: 应用节点列表}`。两类合并时，对
  新进入同一类的同符号应用逐位置入队参数等式；正向同余与反向单射共用一个工作
  队列，直到不动点。
- **证明**：证明森林（proof forest）。每次真正合并记录一条边（输入等式、正向
  同余步或单射步），`explain` 在森林中找最近公共祖先取链；同余边递归展开参数
  子证明，单射边附带“输出相等”子证明（带备忘）。
- **回滚**：每次变更操作前做状态快照（并查集、签名表、父表、单射索引、
  forbidden 表、输入/不等/单射列表等），失败时整体恢复。快照是该操作状态量的
  O(n) 复制；5000 节点上限下代价可忽略。
- **递归深度**：`explain` / 验证器按项深度递归，必要时上调
  `sys.setrecursionlimit`（只升不降，界为 `4 * 节点数 + 100`）。

## 已知限制

- 只实现等式 + 无解释函数符（含可选单射）+ distinct 约束，不含算术、数组等
  其他理论，不假定满射或不同函数符像不相交，也不宣称兼容任何 SMT-LIB 等行业
  标准格式。
- 只处理已通过 `add_term` 加入的有限已有项，推理过程不构造新项。
- 证明规模最坏情形随输入等式数与项深度增长（链式证明未做长度压缩）。
- 快照式回滚在超大节点数下比增量 undo 日志更耗内存；在 5000 节点上限内无实际
  影响。
- 测试中含两个独立对照：暴力全对固定点闭包，以及对小实例枚举全部商模型
  （检验同余、单射与 distinct）；二者均独立于被测核心，不调用核心取期望值。

## 文件

| 文件 | 说明 |
| --- | --- |
| `congruence_closure.py` | 核心库（数据结构、证明、验证器、错误类型） |
| `tests/test_congruence.py` | 单元测试 + 暴力闭包与穷举商模型交叉验证 |
| `demo.py` | 固定输入演示：正向证明、批次冲突回滚、非法输入拒绝 |
| `demo_iteration.py` | 本轮演示：嵌套单射反推、单射冲突回滚、未声明函数不反推 |
