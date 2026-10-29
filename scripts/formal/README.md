# 参考 Lean 复核

这里核验作者参考形式化，不评判候选答卷，也不代表人工审定。每题 `formal/manifest.json` 固定该题的 task、reference、rubric、COVERAGE 字节散列、显式模块顺序和 Lean 源码散列。`CurrentAudit.lean` 是共用模板生成的逐题审计入口；联合作者 Audit 和旧 R001 审计保留为历史证据。

需要 Python 3.10+、Lean **4.29.1**，以及一个已有的 Lake 依赖项目。该项目的 `lake-manifest.json` 必须包含 Mathlib 修订 **5e932f97dd25535344f80f9dd8da3aab83df0fe6**，对应依赖已有可用编译缓存，Mathlib 的实际 Git HEAD 相同且 tracked sources 无改动。验证器记录锁文件、实际修订、tracked diff 状态、Lean 二进制和直接依赖缓存散列。它不下载依赖、不重编 Mathlib，也不写入依赖项目。

以上是兼容既有证据的默认 profile `lean-4.29.1`；旧 manifest 无需增加字段，旧 `CurrentAudit.lean` 模板及依赖收据格式保持不变。另有代码内固定白名单 profile `lean-4.36.0-rc1-tauceti`，用于明确依赖公开 TauCeti 的独立题目。该 profile 的 manifest 必须同时声明：

```json
{
  "verification_profile": "lean-4.36.0-rc1-tauceti",
  "lean_toolchain": "leanprover/lean4:v4.36.0-rc1",
  "mathlib_revision": "2cabef97b63d3275776b8b060d802de6a6fa1055",
  "tauceti_revision": "ab0153c648bc0f1364ea268fc806793beb01473a"
}
```

新 profile 的依赖项目须有相同 `lean-toolchain`，锁定 `.lake/packages/TauCeti`、Mathlib 及其八个传递依赖；全部十包的名称和精确修订由验证器代码中的白名单固定，不能由 manifest 扩大。各包必须是独立 Git checkout，HEAD 精确相符且 tracked sources 无改动。包目录可链接到已有的固定 checkout；依赖项目自身的构建目录仍不可信。TauCeti 和 Mathlib 必须已有编译库；直接导入的缓存仍逐项检查并记录散列。

新 profile 使用独立 `audit-4.36.lean.in`，生成方式为 `render_audit(ordered_modules, "lean-4.36.0-rc1-tauceti")`。它对所有审计根调用公开 `Lean.collectAxioms` 并取完整公理并集，保持相同的三公理白名单和私有声明覆盖。用共用 `verify.py --manifest … --dependency-root … --lean … --out …` 运行；一次调用只能选择同一 profile。新配置不改变默认题集或旧 profile，未知 profile、部分迁移及 profile/依赖混用均拒绝。

默认公开二十题各用独立的新输出目录：

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

独立题集中的 `MG-P001` 等 `MG-P` 三位题号，以及 Lean 对齐题集的 `MG-F101` 等 `MG-F` 三位题号，也使用这个入口和相同的文件、公理审计合同；它们不自动加入默认二十题清单。现行全部 41 题的覆盖另见[习题账本](../../exercises/instructor-guide.md)。编译报告的 `passed` 只表示清单内模块通过核验。是否覆盖完整题面，仍须逐项核对 COVERAGE 与语义审查，不能将辅助模块通过改写为整题形式化完成。

新增题组 `MG-GR/GP/GF` 和章节卷 `MG-C` 使用 `math-gauge.formal-case/v2`。除有序模块闭包之外，v2 绑定当前 `case.json`、题面、参考、评分标准、题组合同及全部候选附件；章节卷的 `candidate/task.md` 也按实际路径绑定。每个 `formal/alignment.json` 必须与合同的阶段或义务逐项对应，记录实际声明、假设、量词、定义域、结论、表示方式、依赖和未完成范围。`complete` 项必须列出声明且没有已知缺口；部分覆盖如实使用 `partial` 或 `pending`。

先写真实证明、`COVERAGE.md` 和逐项对应表，再显式列出模块生成冻结清单：

```sh
python3 scripts/formal/prepare_author.py \
  --case drafts/progressive-groups-20261030/MG-GR103 \
  --module BlockFixedPoints --module TransferBoundaries
```

该命令只生成清单及审计源码，不编译也不生成覆盖结论。随后用上面的共用 `verify.py` 在新输出目录核验。v2 审计显式模块内的全部本地声明，包括非 `MathGauge` 命名空间和私有声明；对应表引用的声明必须实际出现在编译后的清单中。依赖包的公理仍由每个根的完整依赖闭包检查。原 v1 模板、历史源码与报告不改写。

清单一致、声明存在和编译通过都不能自动证明题面等价。语义复核须检查每项的实际定理类型和定义展开，尤其是量词顺序、空域、严格/非严格边界、无穷值、代表元选择、反例满足的全部前提，以及前序题的加强条件是否被误带入。作者自述、独立 AI 审核与人工批准分别记录。

v1 动态审计遍历实际载入的全部 `MathGauge` 常量；v2 遍历显式本地模块的所有命名空间。两者均包含恢复私有名称后的辅助声明、定义、实例、归纳类型、生成声明和定理，遍历全部根的完整公理依赖闭包，仅允许 `propext`、`Classical.choice`、`Quot.sound`。结果中的声明数不能称为定理数。`declarations.json` 分别记录每个声明的名称、原用户名称、模块和种类。

新增43份试卷的[作者证据账本](../../results/author-lean-20261030/README.md)将固定输入、逐项语义审核和编译报告分别绑定。冻结参考或原作者合同中的“当时未生成 Lean”是历史状态；本轮增补状态以该账本和当前 `formal/` 为准，不能改写冻结参考制造事前已有证明的记录。

每题 `report.json` 记录原始命令、源码/日志/olean 散列及公理审计；总报告记录逐题状态和 manifest 散列。坏散列、题目绑定变化、未证明占位符、缺失依赖、错误模块顺序、被替换的审计源码或额外公理都会失败。源码或依赖身份变化后，旧报告不能直接复用。

必要工程合同测试：

```sh
python3 -m unittest discover -s tests -p test_formal_verifier.py
MATH_GAUGE_TEST_DEPENDENCY_ROOT=/absolute/path/to/pinned-dependency-project \
  python3 -m unittest discover -s tests -p test_formal_verifier.py
MATH_GAUGE_TEST_TAUCETI_ROOT=/absolute/path/to/pinned-tauceti-dependency-project \
  MATH_GAUGE_TEST_TAUCETI_LEAN=/absolute/path/to/lean-4.36.0-rc1 \
  python3 -m unittest discover -s tests -p test_formal_verifier.py
```

后两条分别在对应 profile 下真实编译小样例，验证 private helpers 的覆盖、额外 axiom 的拒绝及外部 LEAN_PATH 的排除；4.36 另检查模块系统中未使用的 private axiom。缓存复用只限现有依赖；实际题目模块由当前固定源码重新编译。覆盖的数学范围与可选旁支边界由逐题 COVERAGE 和语义审核说明，不能由编译或声明总数替代。

如果只改逐题 COVERAGE 的呈现，旧编译报告保留原字节。`rebind_coverage.py` 可在写入新 ledger 前重查原模块、CurrentAudit、三份冻结输入、编译器、依赖缓存、原编译产物和日志，只允许 manifest 的 `coverage.sha256` 改变。它保存旧 manifest/ledger，并生成 `evidence-reuse.json`；current-formal 同时指向原编译报告与该重绑定收据。任何 Lean 源码、审计或依赖变化都要求重新编译，不能使用该文档重绑定流程。
