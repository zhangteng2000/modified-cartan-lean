# Modified Cartan — Lean 4 + mathlib

修订稿的全部 19 项带标签结果已有完整证明，定义和补充最优性结论也已核对。包括一般分割定理、精确递推半径吸收、五函数锐定理、R₅ = 2 − √3、完整高斯反例，以及环面和射影空间的几何应用。

项目对应最新的 paper.tex；旧稿保存在 manuscripts/paper-2026-09-18.tex。[修订对比](docs/REVISION_2026-09-19.md)记录了表述修改和 C-class 的 region 用词。原稿常数、半径、不连通开集、直径 ≤ log 3 的端点和双向等价均予保留。

- [最终报告](docs/FINAL_REPORT.md)：逐项论文标签、证明名称、来源文件、公理检查和差异说明。
- [覆盖清单](FORMALIZATION_STATUS.md)及[机器可读对应表](verification/manuscript-coverage.json)。
- [构建与审计结果](verification/result.json)、[全部定理公理清单](verification/axiom-summary.json)。
- [证明依赖图](docs/DEPENDENCIES.md)、[完整编译依赖](verification/dependencies.json)。
- [几何模型说明](docs/GEOMETRIC_MODEL.md)及[经典 Cartan 证明](docs/CARTAN_EXTRACTION.md)。

Lean 固定为 v4.34.0-rc1，mathlib 固定为 de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11。所有本地定理逐一运行 #print axioms，允许的基础公理仅为 propext、Classical.choice 和 Quot.sound；没有论文专属公理或未完成证明。

## 本机复核

在本项目目录运行：

```powershell
.\verify.ps1 -Fresh
```

脚本核对稿件哈希、全部论文标签、证明项、依赖版本和依赖工作树，在新的临时目录全量重建本地模块，然后运行 ManuscriptCheck.lean 和 Audit.lean。默认每批至多编译四个就绪模块，避免本机高并发下的库文件读取失败。最后仍执行完整的 lake build。

mathlib 缓存默认为 E:/Lean 4/Sendov_conjecture_explicit_n0/.lake/packages。可使用 -PackageRoot 指定其他同版本缓存的**绝对路径**。固定依赖的已编译缓存会复用，本地证明模块从空构建目录重建。日志和哈希保存在脚本输出的验证目录；本次交付的完整记录也存于 verification/。

## 在其他电脑复核

安装 elan 后，在项目目录执行：

```text
lake exe cache get
lake build
lake env lean ManuscriptCheck.lean
lake env lean Audit.lean
```

Windows 上也可在获得缓存后运行：

```powershell
.\verify.ps1 -PackageRoot (Resolve-Path '.lake/packages').Path -Fresh
```

工具链、依赖配置和源文件都在仓库中。脚本不修改 Lean/mathlib 的保护或证明检查设置。

当前完整工作副本位于 C:/Users/HUAWEI/AppData/Local/ModifiedCartanFormalization/outputs/ModifiedCartan。Documents 下的原副本保留为先前快照；迁移原因与完整记录见修订说明。完整 Git 历史保存在本地仓库和 [GitHub 仓库](https://github.com/zhangteng2000/modified-cartan-lean)中。
