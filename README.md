# congruence_closure — 函数符号等式的同余闭包

离线、可复用、可产生证明的同余闭包（congruence closure）库，用于程序证明内核：
对无解释函数符号的等式理论做判定，并为每个推出的等式/矛盾给出可独立验证的证明。

- Python 3.14.7，仅标准库，无任何第三方依赖，完全离线。
- 核心模块：`congruence_closure.py`（单文件，可直接 `import`）。
- 测试：`tests/test_congruence.py`（原回归）、`tests/test_scopes.py`（push/pop 作用域）；
  演示：`demo.py`。

## 运行

```bash
python -m unittest discover -s tests -v
python demo.py
```

## 接口

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

# 分层假设（交互验证）：等式、不等式和新增项都属于当前层
cc.push()                                # 进入新假设层，返回新深度；O(1)，不复制项图
cc.assert_equal(a, b)                    # 本层假设：推出 f(a) = f(b) 等结论
cc.pop()                                 # 撤出本层：相等类、父签名、证明森林、冲突状态全部回到 push 前
cc.scope_depth                           # 当前开放的假设层数（0 = 底层）
with cc.scope():                         # push/pop 的上下文管理器形式（异常也会 pop）
    cc.assert_equal(a, b)
```

只读视图：`cc.terms`（节点 id → `(func, arg_ids)`，含已 pop 层的墓碑项）、`cc.input_equalities`、
`cc.distinct_assertions`、`cc.node_count`（当前有效节点数）、`cc.max_nodes`、`cc.scope_depth`、
`cc.term_of(nid)`。
辅助：`term_to_str(nid, terms)`、`proof_to_str(proof, terms)` 用于打印。

### 作用域（push/pop）语义

- **分层断言**：`push` 之后的所有等式、不等式和新增项都属于当前层；可嵌套。
  内层可以自由引用外层项。
- **pop 完全撤销**：相等类（并查集）、父签名表、证明森林（解释图）、冲突
  （distinct）状态精确回到对应 `push` 之前；`input_equalities` /
  `distinct_assertions` 截断到进入时的前缀。
- **句柄失效**：节点 id 单调分配、绝不复用。pop 后内层项的 id 保留为墓碑，
  任何操作使用旧句柄抛 `StaleNodeError`（`UnknownNodeError` 子类）；之后新建的
  同形项得到全新 id，旧句柄不会误指它。
- **证明只含有效断言**：`explain` 返回的证明只引用当前仍有效的输入等式；
  已撤销层的边不会出现在外层结论的证明里。
- **冲突层可 pop**：层内操作冲突（`ContradictionError`）只回滚该操作，层仍然
  有效，可继续断言或直接 `pop`。
- **底层 pop 报错**：没有开放层时 `pop` 抛 `ScopeError`，底层状态不变。

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
  `pop` 同样原子：整层一次性撤销。
- **错误语义**（均可定位到具体参数，不静默纠正）：
  - `ValidationError`：非法参数（节点 id 非 int、为 bool、为 float 含 NaN/Inf；
    函数符非非空字符串；批次 op 格式错误并标注下标等）。
  - `UnknownNodeError`：节点 id 越界。
  - `StaleNodeError`（`UnknownNodeError` 子类）：句柄来自已被 pop 的层。
  - `ScopeError`：底层无层可 pop。
  - `NodeLimitError`：共享 DAG 当前有效节点数已达 `max_nodes`（默认 5000）上限。
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
- **证明**：证明森林（proof forest）。每次合并记录一条边（输入等式或同余步），
  `explain` 在森林中找最近公共祖先取链，同余边递归展开参数子证明（带备忘）。
- **回滚**：每次变更操作前做状态快照（并查集、签名表、父表、forbidden 表、
  输入/不等列表等），失败时整体恢复。快照是该操作状态量的 O(n) 复制，
  换来实现的简单与回滚的绝对可靠；5000 节点上限下代价可忽略。
- **作用域撤销**：`push` 本身 O(1)，不复制项图。每个层维护一份变更日志
  （undo journal）：并查集/大小/证明森林按下标、签名表/父表/forbidden/
  hash-cons/元数表按键，只记录本层**首次**被写位置的旧值；`pop` 回放日志
  精确复原，再把输入/不等列表截断到进入时的前缀、把本层新建项打成墓碑。
  日志与操作级快照正交：失败操作由快照恢复后，日志里保留的旧值仍然正确。
- **递归深度**：`explain` / 验证器按项深度递归，必要时上调
  `sys.setrecursionlimit`（只升不降，界为 `4 * 节点数 + 100`）。

## 已知限制

- 只实现本题契约内的同余闭包（等式 + 无解释函数符 + distinct 约束），
  不含算术、数组等其他理论，也不做函数符单射性等额外推理；不宣称兼容任何
  SMT-LIB 等行业标准格式。
- 证明规模最坏情形随输入等式数与项深度增长（链式证明未做长度压缩）。
- 快照式回滚在超大节点数下比增量 undo 日志更耗内存；在 5000 节点上限内无实际影响。
- 已 pop 层的项以墓碑形式保留（节点 id 不复用），`terms` 表与并查集数组不会
  因 pop 而缩短；`max_nodes` 按当前**有效**节点数计。频繁 push/pop 且每层大量
  新建项时内存随历史总量增长。
- 测试中的参考实现（`tests/test_congruence.py` 内的全对暴力闭包）独立于被测核心，
  仅用于小实例交叉验证；`tests/test_scopes.py` 把每个操作前缀的有效断言重放进
  全新闭包实例逐对比较，并独立检查证明叶子都属于当前有效层。

## 文件

| 文件 | 说明 |
| --- | --- |
| `congruence_closure.py` | 核心库（数据结构、证明、验证器、push/pop 作用域、错误类型） |
| `tests/test_congruence.py` | 单元测试 + 独立参考闭包交叉验证 |
| `tests/test_scopes.py` | push/pop 作用域测试 + 操作前缀级全新实例交叉验证 |
| `demo.py` | 固定输入演示：正常证明、作用域压入/撤回、批次冲突回滚、非法输入与底层 pop 拒绝 |
