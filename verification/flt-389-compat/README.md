# 389.a1：FLT 与 Stoll 兼容验证

`RankPart389.lean` 使用同仓库 `verification/flt-long-twist` 的 `ExactWitness` 和 `ExternalDataBridge`，以及 `BSD.RankTwo.FromModularity`，证明 `BSD.RankTwo.FLTAdapter.weakBSD389 : BSD.RankPart BSD.RankTwo.curve`；同时得到无需外加假设的 `integral_modular_model_data389`。项目既有 `BSD.RankTwo389.rational_finrank_eq_two` 证明同一曲线的有理点群秩为 2。`RankPart` 是该曲线自身 L 级数的亚纯延拓在中心的阶等于代数秩，不是完整 BSD 前导系数公式。

依赖版本：Lean 4.33.1，mathlib `0df444a360eaa60ab8c11dca51a86af692955474`，Stoll EllipticCurves `7c476bd2eea67d7966f5f14e58da8b3f70ee59f8`，外部 FLT 版本及许可见相邻 `flt-long-twist/README.md`。`STOLL-LICENSE` 是 Stoll 固定版本 Apache 2.0 许可证原文，`stoll-compat.patch` 是针对该版本的合并补丁；未复制上游完整源码或构建产物。

将固定 Stoll 版本的仓库根作为工作目录的父目录，使上游的 `EllipticCurves/` 源码目录位于该父目录内，然后执行 `git apply --check stoll-compat.patch` 与 `git apply stoll-compat.patch`（补丁路径按实际位置填写）。在全新隔离导出的固定版本上，这两步已实测成功，受影响 26 个 Stoll 源逐项 SHA 与当次编译输入一致；项目侧 11 个重新编译的源与固定 Git 树相同。`plan.txt` 按依赖顺序列出历史严格重编的 37 个模块。

原始 CPU 命令、日志、每模块耗时与源码哈希见 `.agents/evidence/flt-389-v4-20261124/`。历史 `build.sh` 依赖指定 CPU 临时路径和已有 FLT/mathlib 缓存，历史 `patch-compat.py` 还依赖此前手工实例改名，不能作为单独补丁重建流程；可移植环境搭建及全传递依赖从源码重建尚未验证。当前已完成的是 Lean 定向编译及标准公理检查，独立 checker 正负挑战和独立 proof DAG 重放尚待验收。
