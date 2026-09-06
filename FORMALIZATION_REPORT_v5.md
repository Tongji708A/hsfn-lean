# Lean 4 形式化报告 v5 — R260409 第五期（ultracode 扇出，2026-09-05 夜 — 09-06，DESKTOP-BRJD313）

承接 v4。工程 `E:\claude-lean-work\hsfnlean\`，工具链 `leanprover/lean4:v4.31.0`，mathlib `v4.31.0`（自 pilot 起未升级）。
GitHub `Tongji708A/hsfn-lean`（private，main）；NAS 远端 `nas/main`；同步盘存档 `061/.../lean/`。

## 结果

- `lake build`：**Build completed successfully (8600 jobs)**，零 `sorry` 警告，零 `admit`、零 `native_decide`、零自定义 axiom。
- `AxiomCheck.lean`：当时发出 560 条指令。**该数字不成立**——2026-09-06 codex 复核发现名字提取正则不含 Unicode，`swapWμ_*` 六条被截断成定义 `HSFN.Calc.swapW`，实为 555 个互异目标。第六期已用 Unicode 安全提取重做，结果见文末。
- **40 个模块、15753 行**（pilot 3 模块 1133 行 → 今日 40 模块）。

## 第五期新增 23 个模块

用 ultracode 多 agent 编排，两条 workflow 并行，每个目标走四段流水线，每段换人：
**① 写陈述（禁止证明）→ ② 对着论文做忠实性审计（可改陈述，仍禁止证明）→ ③ 只补证明（禁止改陈述）→ ④ 对抗复检（自跑 typecheck、grep 作弊构造、重算数值见证、判 ACCEPT / ACCEPT_WITH_GAPS / REJECT）**。
并发安全靠三条硬约束：每 agent 只准改一个文件、只准 `lake env lean` 单文件检查、禁 `lake build`。

| 模块 | 论文标签 | 行数 |
|---|---|---|
| `Equidistance` | lem:equidistance（必要方向，Gram 引擎，界紧） | 259 |
| `Locator` | prop:locator-II（位长、覆盖与区分能力、极限、= 1 当且仅当 N 是 2 的幂） | 433 |
| `TierLocator` | 附录 subsec:duality 的 tier locator | 260 |
| `Protocol` | thm:deg-I、prop:conn-price(ii) 两半 | 518 |
| `SecurityRec` | thm:security（确定性递归、唯一性、两个实例） | 374 |
| `DenseUpdate` | thm:appendix-update-correct（veto 文法 DFS 单圈） | 554 |
| `ClawFree` | def:realization 用到的 claw-free | 207 |
| `TreeDecomp` | lem:tw-nec 上界（六条款手写树分解） | 469 |
| `AvgDegree` | thm:deg-II(iii)（严格递增、极限 N+1） | 195 |
| `PartialFill` | subsec:partial-fill（塌缩到 (N+1)V） | 255 |
| `IFS` | thm:dim-II 的几何核（压缩、角映像、开集条件、Moran 方程） | 319 |
| `RunningExample` | N=5, m=3 回归见证（含 `(graph 5 3).diam = 5`） | 355 |
| `RelabelGroup` | lem:dup-digit(ii) 的群结构与 wreath 复合律 | 569 |
| `Delay` | thm:delay（两侧显式界，不用 O(1)） | 241 |
| `Chordal` | 块图的弦性（并证了假设类非空） | 202 |
| `EdgeCut` | lem:edge-cut（节点级 N 条上行链、胞级 1+σ） | 749 |
| `GraftIso` | thm:graft-iso(i)(ii)（前缀替换、标记搬运、同构） | 602 |
| `KpiAffine` | prop:kpi-affine（四个仿射指标 + O(1) 维护） | 748 |
| `CanonWord` | prop:canon-word（规范词可达、状态空间闭合） | 677 |
| `Commute` | prop:commute + **守卫读必要性的具体反例** | 620 |
| `RelExact` | prop:rel-exact（可靠性非剖面可算的精确有理见证） | 1388 |
| `Derived` | 派生 swap = 三个 graft 的交换律与对合性 | 618 |
| `Spacetime` | def:spacetime-coordinate、prop:coordinate-persistence(ii)(iv) 的搬运 | 475 |

## 复检口径

23 个模块的自评为 22 个 ACCEPT、1 个 ACCEPT_WITH_GAPS（`Commute`，缺口在 scope 内且写进 docstring）。
**Claude 未采信自评**：逐文件重跑 `lake env lean`、重跑 cheat 正则、并做跨文件重名扫描。发现并修掉两处**只有全量 build 才会暴露的硬冲突**：
- `HSFN.Calc.movedSlots` 在 `GraftIso`（`Set`）与 `EdgeCut`（`Finset`）各定义一次 → 前者改名 `movedSlotSet`；
- `HSFN.Calc.Gen` 在 `CanonWord` 与 `Commute` 各定义一次 → 前者改名 `Letter`。
另有一次 cheat 正则误报（`PartialFill` 文档串里"axiom audit reports only…"一句），非缺陷。

## 审计段的科学价值

见 `notes/LEAN_ULTRACODE_AUDIT_260906.md`。要点：审计段推翻了**任务书本身的两处错误规格**（`ClawFree` 的邻域覆盖式对 tier ≥ 2 为假，需并上 `parF`；`EdgeCut` 的节点级与胞级是两个不同的移动集），并修掉 9 处"编译通过但科学上空洞"的陈述，典型如 `RunningExample` 里 `2*3-1 = 5` 这种 `rfl` 级恒等式被换成 `(graph 5 3).diam = 5`、`TreeDecomp` 的合取原本根本不构成树分解。
**结论：只看"零 sorry、零 error"验收形式化是不够的。**

## 覆盖普查与剩余工作

见 `notes/LEAN_COVERAGE_CENSUS_260906.md`（按论文标签逐条）。摘要：

- **完全覆盖**：def:address-II / prop:addr-bij、lem:dup-digit、thm:adjacency-II、prop:locator-II、thm:distance-II、thm:deg-II 三条款、lem:family-mono、lem:tree-embed、thm:update-main、prop:threshold-b 三项、cor:threshold-II、thm:threshold。
- **完全未覆盖**：lem:block-image、prop:blockcut-caveat、thm:blockcut、prop:two-full-sep、lem:gate、thm:lifting、lem:staging、lem:mask-transport、lem:gather、lem:descent。障碍只有两个，且都不是 HSFN 特有的：mathlib 没有块 / 块-割树 / 2-连通（唯一的 `IsBlock` 是群作用的），工程里没有 `def:realization` 的实现语义。另外 mathlib v4.31 也没有树宽、没有顶点连通度。
- **下一步三个最高价值目标**：T1 `Fintype.card (DNode N m) = Dense.V N m`（最便宜的高杠杆，一举把 thm:node-count 升级为关于真实节点集的事实并关掉 prop:consensus-tree(1)(4)）；T2 有限图的块抽象（同时解锁六个标签）；T3 `dimH 𝒮Δ_N ≤ log₂ N`（绕开缺失的自相似集 API，把吸引子直接定义成嵌套交）。
- **六处内容偏薄需处理**：`Protocol` 的 thm:deg-I 是关于假想树的（从未构造实例）；`PartialFill` 只证塌缩不证修正且见证在 N=2；`IFS` 挂着 thm:dim-II 标签却无维数陈述且 docstring 未声明；`TierLocator` 无理由地弱于其 HSFN 孪生；`RunningExample` 的标签清单夸大；`TreeDecomp` 证了两条引理又弃之不用。

## 论文侧

附录 E 机器化段落与 `tab:verification` 行按本期范围重写（见 UPLIFT §X）。

---

# 第六期附记：内容偏薄的六处修复 + T1 落地（2026-09-06 上午）

针对上文第五节列出的六处"编译通过但内容偏薄"，另开一条 workflow（7 个目标 × 修复 + 对抗复检 = 14 个 agent）。
自评 6 个 CLOSED、1 个 PARTIAL（`TreeDecomp`，缺口已如实写进 docstring）；无任何弱化、无不诚实 docstring。Claude 逐文件复检并重跑跨文件重名扫描（归零）。

| 模块 | 处置 |
|---|---|
| **`DenseCard`（新）** | `Fintype.card (DNode N m) = Dense.V N m`，即 **T1**。thm:node-count 从"关于 ℕ 递归的事实"升级为关于真实节点集的事实；顺带 `N_dvd_card_DNode` 与 `card_CNode_eq_V_div`（prop:consensus-tree 第 1 项） |
| `Protocol` | 构造了稠密胞树实例 `Cell N m` / `parentCell` / `rootedTree_dense`，用 `DenseUpdate` 已证的分支事实 discharge 掉假设，给出 `dense_degree_root/internal/leaf` 三条**不带分支假设**的推论，外加 `dnodeEquivCell`、`dense_two_mul_card_edges`、`dense_induce_compl_reachable`。thm:deg-I 不再是关于假想树的 |
| `IFS` | **真证出维数上界**：吸引子定义为嵌套交 `attractor = ⋂ stage`，证 `isCompact_attractor`、`attractor_nonempty`、`hausdorffMeasure_attractor_le_one`，最终 `dimH_attractor_le : dimH (attractor N) ≤ logb 2 N`。下界仍缺（需质量分布原理），已写进 docstring |
| `TierLocator` | 补上论文那句的一般形式（≤ 3/2、仅 N=3 取等、沿 N=2^k 的行为），不再只有两个 norm_num 事实 |
| `TreeDecomp` | 接线两条孤儿引理，补 m=1 条款与"团必落在某袋内"的下界论证。判 PARTIAL，剩余缺口已披露 |
| `PartialFill` | 见证换到论文区间 N≥3，且用**非整数** k̄ 展示修正项严格大于 k̄²，证明它不是装饰 |
| `RunningExample` | docstring 改为如实说明它是回归见证层，每条定理注明所实例化的一般结果与其所在模块；并补齐论文运行例里其余可判定的数字 |

## 第六期结果

- **41 个模块、17941 行**。`lake build`：**Build completed successfully (8601 jobs)**，零 sorry。
- `AxiomCheck.lean` 覆盖**全部模块的全部公开定理，共 800 条**（自动生成，非人工挑选），全部落在 `propext`、`Classical.choice`、`Quot.sound` 之内，**25 条完全不依赖任何公理**（旧稿写 26，来自坏掉的抽取器把定义 HSFN.Par 当成定理；Unicode 安全版重跑后为 25），无 `sorryAx`。输出 `AXIOMS_260906.txt`。
- 仓库：**https://github.com/Tongji708A/hsfn-lean（public）**，commit `a74a269`；NAS `2e682e4`。
