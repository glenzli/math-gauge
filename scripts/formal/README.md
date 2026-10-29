# 参考 Lean 复核

这里核验作者参考形式化，不评判候选答卷，也不代表人工审定。每题 `formal/manifest.json` 固定该题的 task、reference、rubric、COVERAGE 字节散列、显式模块顺序和 Lean 源码散列。`CurrentAudit.lean` 是共用模板生成的逐题审计入口；联合作者 Audit 和旧 R001 审计保留为历史证据。

需要 Python 3.10+、Lean **4.29.1**，以及一个已有的 Lake 依赖项目。该项目的 `lake-manifest.json` 必须包含 Mathlib 修订 **5e932f97dd25535344f80f9dd8da3aab83df0fe6**，对应依赖已有可用编译缓存，Mathlib 的实际 Git HEAD 相同且 tracked sources 无改动。验证器记录锁文件、实际修订、tracked diff 状态、Lean 二进制和直接依赖缓存散列。它不下载依赖、不重编 Mathlib，也不写入依赖项目。

全部十题各用独立的新输出目录：

```sh
python3 scripts/formal/verify_suite.py \
  --dependency-root /absolute/path/to/pinned-dependency-project \
  --out /absolute/path/to/new-verification-output \
  --jobs 2
```

默认使用 PATH 上的 Lean；也可显式传 `--lean /absolute/path/to/lean`。逐题入口支持同样的依赖与输出参数：

```sh
python3 cases/public/MG-R001/formal/verify.py \
  --dependency-root /absolute/path/to/pinned-dependency-project \
  --out /absolute/path/to/new-r001-output
```

共用入口也接受一个或多个显式 `--manifest`。`--out` 必须尚不存在，不能覆盖以前的日志或复用题目输出。每题源码复制到自己的 fresh sources 目录，olean 和日志另存；只把该题 olean、依赖包缓存和 Lean 标准库加入 LEAN_PATH。题目源码旁的旧 olean、兄弟题构建、环境里的 LEAN_PATH，以及依赖项目自身的构建库均不进入搜索路径。共享数学辅助模块须在每题 manifest 的闭包中明确出现并锁定相同散列。

动态审计遍历实际载入的全部 `MathGauge` 常量，包括恢复私有名称后的辅助声明、定义、实例、归纳类型、生成声明和定理。它验证声明来自该题 manifest 的模块，遍历全部根的完整依赖闭包，仅允许 `propext`、`Classical.choice`、`Quot.sound`。结果中的 `dynamic_declaration_count` 是声明数，不能称为定理数。`declarations.json` 分别记录每个声明的名称、原用户名称、模块和种类。

每题 `report.json` 记录原始命令、源码/日志/olean 散列及公理审计；总报告记录逐题状态和 manifest 散列。坏散列、题目绑定变化、未证明占位符、缺失依赖、错误模块顺序、被替换的审计源码或额外公理都会失败。源码或依赖身份变化后，旧报告不能直接复用。

必要工程合同测试：

```sh
python3 -m unittest discover -s tests -p test_formal_verifier.py
MATH_GAUGE_TEST_DEPENDENCY_ROOT=/absolute/path/to/pinned-dependency-project \
  python3 -m unittest discover -s tests -p test_formal_verifier.py
```

第二条还真实编译小样例，验证 private helpers 的覆盖、额外 axiom 的拒绝及外部 LEAN_PATH 的排除。缓存复用只限现有依赖；实际题目模块由当前固定源码重新编译。覆盖的数学范围与可选旁支边界由逐题 COVERAGE 和语义审核说明，不能由编译或声明总数替代。

如果只改逐题 COVERAGE 的呈现，旧编译报告保留原字节。`rebind_coverage.py` 可在写入新 ledger 前重查原模块、CurrentAudit、三份冻结输入、编译器、依赖缓存、原编译产物和日志，只允许 manifest 的 `coverage.sha256` 改变。它保存旧 manifest/ledger，并生成 `evidence-reuse.json`；current-formal 同时指向原编译报告与该重绑定收据。任何 Lean 源码、审计或依赖变化都要求重新编译，不能使用该文档重绑定流程。
