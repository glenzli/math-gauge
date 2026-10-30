# 作者 Lean 与证据复核

这里核验作者参考形式化，不运行候选模型，也不代表人工审定。唯一题目目录是 [`cases/suite.json`](../../cases/suite.json)，包含 43 份当前试卷。作者证据及独立语义审核见 [`verification/author/`](../../verification/author/README.md)。42 份试卷完整覆盖；GP003 的 S5 保留明确缺口，372 项义务中完成 371 项。编译通过、完整语义对应、独立 AI 审核和人工批准分别记录。

## 离线复核已保存的证据

普通源码导出或浅克隆只需 Python 3.10+，不需要 Git 历史、Lean 安装、临时构建目录或依赖缓存：

```sh
python3 scripts/formal/check_evidence.py
```

该命令不调用 Git、Lean 或模型，不写文件。它检查当前清单、原始编译报告、保存的编译及公理审计日志、实际声明清单、逐项对应表和独立语义审核的全部有效源码散列，并与当前证据账本比较。原始报告中的临时绝对路径只是当时执行的记录，不要求这些路径今天仍然存在。已保存的 olean 散列和依赖收据不等于重新检查当前机器上的编译器或缓存。

每题 `formal/manifest.json` 使用 `math-gauge.formal-case/v2`，固定当前 `case.json`、task、reference、rubric、题组合同、全部候选附件、COVERAGE、逐项 alignment、显式有序模块和生成的 CurrentAudit。题目声明 `path_base: "case"`，其中的材料路径相对本题目录。旧 suite 相对路径仍用于小型兼容合同测试，不保留第二份历史题库。

42份未变题目沿用严格的元数据迁移绑定：数学材料、候选附件、Lean源码、COVERAGE、alignment和原始编译证据均保持原字节。`checked-case.json`、`checked-manifest.json`与`verification/author/checked-ledger.json`保留原身份，`input-binding.json`记录唯一允许的目录与派生元数据变化。此路径不允许把源码修改重绑到旧编译。

GP003使用`recompiled-author-evidence`：真实新编译必须绑定当前清单、源码、日志、完整声明清单和基础公理闭包；当前独立语义审核须绑定这些文件、全部数学输入，逐项给出具体检查，并与完整/部分覆盖状态一致。作者、审核者、编译、人工状态和实际时间分别记录。题面、候选附件、评分和合同保持原散列；参考说明的编辑须由新证据重绑。

修改证明后，先按下文冻结并真实编译，把实际输出的`report.json`、`declarations.json`和`logs/`保存到本题formal目录，再完成独立语义复核。只有这些工作都已完成，才运行：

```sh
python3 scripts/formal/check_evidence.py \
  --bind-recompiled MG-GP003 \
  --semantic-review verification/author/semantic-reviews/MG-GP003.json --write
python3 scripts/formal/check_evidence.py
```

该命令只验证和绑定已有证据，不编译、不生成语义结论。旧的checked身份仅作来源记录，不冒充新证明；其余42题仍逐项验证原编译身份。无需新增历史快照目录或依赖Git历史才能离线检查。

## 编写和冻结作者工程

先写真实证明、`COVERAGE.md` 和逐项 `alignment.json`，再显式按依赖顺序列出模块：

```sh
python3 scripts/formal/prepare_author.py \
  --case cases/proofs/MG-GR103 \
  --module BlockFixedPoints --module TransferBoundaries
```

该命令只生成清单和审计源码，不编译，不自动发现模块，也不生成覆盖结论。每条 alignment 记录实际声明、假设、量词、定义域、结论、表示方式、依赖及未完成范围；它必须覆盖合同中的全部阶段或章节义务。`complete` 必须列出实际声明且没有已知缺口，未闭合部分使用 `partial` 或 `pending`。

## 真实编译

编译需要一个已有、固定依赖且带可用缓存的 Lake 项目。共用入口只将本题全新输出、固定包缓存和 Lean 标准库放入 `LEAN_PATH`。源码旁的旧 olean、兄弟题输出、环境中的 `LEAN_PATH` 和依赖项目自己的构建目录均被排除；输出目录必须尚不存在。

默认 profile 为 `lean-4.29.1`：Lean **4.29.1**，Mathlib 修订 **5e932f97dd25535344f80f9dd8da3aab83df0fe6**。验证器检查锁文件、实际 Mathlib HEAD、tracked sources、编译器与直接依赖缓存身份；不下载依赖或重编 Mathlib。

```sh
python3 scripts/formal/verify.py \
  --manifest cases/proofs/MG-GR001/formal/manifest.json \
  --dependency-root /absolute/path/to/pinned-dependency-project \
  --out /absolute/path/to/new-author-output
```

只有 MG-GP001 使用固定白名单 profile `lean-4.36.0-rc1-tauceti`：

```json
{
  "verification_profile": "lean-4.36.0-rc1-tauceti",
  "lean_toolchain": "leanprover/lean4:v4.36.0-rc1",
  "mathlib_revision": "2cabef97b63d3275776b8b060d802de6a6fa1055",
  "tauceti_revision": "ab0153c648bc0f1364ea268fc806793beb01473a"
}
```

该 profile 的 Lake 项目须使用相同 toolchain，锁定 TauCeti、Mathlib 及八个传递依赖。全部十包的名称和精确修订由 `verify.py` 固定；每包须有独立、干净且 HEAD 相符的 checkout，TauCeti 与 Mathlib 须已有编译库。清单不能扩充依赖政策；未知 profile、部分迁移或混用依赖均拒绝。使用 `--lean /absolute/path/to/lean` 可选择明确的编译器。

`verify_suite.py` 从同一 `cases/suite.json` 读取全部试卷，再按 profile 选择编译子集。默认 profile 选择 42 份；TauCeti profile 选择 GP001 一份。报告明确列出全题库数量、选中数量及未选中的题目；单次通过不代表两个 profile 均已编译。

```sh
python3 scripts/formal/verify_suite.py \
  --dependency-root /absolute/path/to/pinned-dependency-project \
  --profile lean-4.29.1 --out /absolute/path/to/new-default-output --jobs 2
python3 scripts/formal/verify_suite.py \
  --dependency-root /absolute/path/to/pinned-tauceti-project \
  --profile lean-4.36.0-rc1-tauceti \
  --lean /absolute/path/to/lean-4.36.0-rc1 \
  --out /absolute/path/to/new-tauceti-output
```

## 证据边界与合同测试

v2 审计显式模块内所有命名空间的全部本地声明，包括 private helpers、定义、实例、归纳类型和生成声明，并收集每个根的完整公理闭包；只允许 `propext`、`Classical.choice`、`Quot.sound`。对应表引用的声明必须存在于实际编译清单中。`declarations.json` 的数目是声明数，不是定理数。v1 保留为兼容验证合同，使用既有 MathGauge 命名空间审计模板，不对应另一份正式题库。

编译和声明存在都不证明题面等价。独立语义复核须检查实际定理类型和定义展开，包括量词顺序、空域、严格边界、无穷值、代表元选择、反例前提和额外条件。作者自述、独立 AI 审核与人工批准保持区分；作者参考的通过不能代替候选工程验收。

```sh
python3 -m unittest discover -s tests -p test_formal_verifier.py
```

可选的真实内核合同测试使用小型临时 fixture，不重编全部作者模块：

```sh
MATH_GAUGE_TEST_DEPENDENCY_ROOT=/absolute/path/to/pinned-dependency-project \
  python3 -m unittest discover -s tests -p test_formal_verifier.py
MATH_GAUGE_TEST_TAUCETI_ROOT=/absolute/path/to/pinned-tauceti-project \
  MATH_GAUGE_TEST_TAUCETI_LEAN=/absolute/path/to/lean-4.36.0-rc1 \
  python3 -m unittest discover -s tests -p test_formal_verifier.py
```

这些测试检查 private helpers、额外 axiom 和外部 `LEAN_PATH` 的排除。普通离线测试另检查数学或源码变动、元数据越界、报告或审核篡改、缺失声明、局部 axiom、日志与审计清单不一致及合法迁移。没有源码变化时，目录整理复用已保存的真实证据。
