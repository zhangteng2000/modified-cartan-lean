# Modified Cartan — Lean 4 形式化项目

**当前状态：部分完成。论文的分割主定理、一般 Wronskian 定量估计、倒数吸收估计和五函数最优性尚未完成 Lean 证明。**

本项目依据用户提供的 `paper.tex`，使用 Lean 4.34.0-rc1 和固定版本的 mathlib。已证明的结果有实际 Lean 证明项；未完成的中心命题在 `Statements.lean` 中仅定义为 `Prop`，没有被当作公理或已证明定理使用。

已完成的主要内容：

- 圆盘、全纯无零点函数列、紧集上一致收敛、固定主导指标、C-类和分割的定义；C-类至少含两个指标，限制区域保留分割。
- Montel 抽取、Hurwitz 非零极限和连通区域上 C-类经子列抽取后存在两个不同主导指标的完整证明。
- Borel–Nevanlinna 增长引理的完整证明。
- Cartan 圆估计的完整证明，含有限零点分解、带重数的对数平均选圆，以及原稿的幂次下界 `t^γ`。
- 原稿调和包络引理的完整证明，含常数 8、64 和闭圆盘上确界；所需 Harnack 比较直接由 mathlib 的 Poisson 公式推出。
- 对数 Poisson 平均引理的完整证明，允许积分圆周上存在零点，保留精确系数 q 和 q²−1。
- 半径 `2 - sqrt 3` 的代数恒等式和对数公式；递归半径的正性、单调性及吸收证明末尾的常数估计。
- 五函数部分两点核引理的完整证明：核分解、统一正间隙、Poisson 积分和半径极限，适用于开单位圆盘上任意正调和函数。
- 指数和的有限矩判据，包括重复指数的分组；Laurent 多项式沿指数轨道恒零与有限方程组的等价性。
- 在环境坐标中定义 Kobayashi–Royden 伪度量，证明指数轨道包含于目标集合时伪度量为零。
- Wronskian 的常数缩放、线性相关时为零，以及定量估计的单函数情形。
- 预序稳定化引理的完整证明：同一子序列上的商函数收敛或紧集最大值发散、最大等价类计数和不可比较性。

完整覆盖情况见 `FORMALIZATION_STATUS.md`，持续进度与依赖图见 `docs/PROGRESS.md`、`docs/DEPENDENCIES.md`。编译通过不表示所有论文命题已经证明。

## 本机复核

在此目录运行：

```powershell
.\verify.ps1 -Fresh
```

脚本读取本机已有的 mathlib 依赖缓存，核对各仓库提交号，在临时目录复制并哈希核对源文件，执行真实的 `lake build`，然后用 `#print axioms` 审计每个本地定理。日志、源文件哈希和结果 JSON 写入脚本输出的临时目录。交付时的日志另存于 `verification/`。

本机缓存默认为 `E:\Lean 4\Sendov_conjecture_explicit_n0\.lake\packages`；可通过 `-PackageRoot` 指定同版本缓存。构建采用临时目录，是因为本次操作中 PowerShell 在 Documents 下创建编译产物失败；Lean 源文件保留在交付目录。

## 在其他电脑使用

安装 elan 后，在项目目录运行：

```text
lake exe cache get
lake build
lake env lean Audit.lean
```

`lean-toolchain`、`lakefile.toml` 和 `lake-manifest.json` 固定版本。`Audit.lean` 罗列所有本地定理。当前允许的基础公理仅为 `propext`、`Classical.choice`、`Quot.sound`。

局部一致收敛采用 mathlib 的标准定义，并证明了与本项目紧集表述的等价性：[mathlib 官方文档](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/LocallyUniformConvergence.html)。
