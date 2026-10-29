# 固定环境与移植记录

本题当前完整证明使用共享验证器的 `lean-4.36.0-rc1-tauceti` profile。默认题集的 Lean 4.29.1／Mathlib 5e932f97 配置未改变；外部库没有硬移植进默认 Mathlib。

原11个几何模块在4.29.1下已经通过共享验证，并保留于 `../history/round2-lean4.29/` 和 `evidence/round2-20261029/`。转到4.36的源码改动限于：

- `VertexDeletion` 将 `Mathlib.Tactic` 改为实际使用的 Field、Linarith、NormNum、Ring、FieldSimp imports，并为删点同胚的 `Homeomorph.setCongr` 显式给出集合等式类型；
- `DeletionConeGluing`、`SuspensionRetime` 使用 `Topology.IsQuotientMap.of_surjective_continuous` 的新命名空间；
- `TwoConeOpenCover` 使用新 API 名 `continuous_finsetSum`。

定义、对象、量词及结论没有改变。原悬挂移植的许可证和 NOTICE 保留于 `vendor/`。

新增六个几何／同调桥通过真实坐标同胚接到 TauCeti；没有假设 CW、Hurewicz 结论或目标 contractibility certificate。`FiniteLocalChains`、`FiniteBoundaryMatrix`、`FiniteMatrixCriterion`、`FiniteLocalCriterion` 将桥的结论接成有限整数矩阵的原题判据。所有新增模块均在当前manifest中按依赖顺序重编译。

完整依赖版本和精确来源在 `manifest.json`、`tauceti-dependency-audit.json` 与共享验证报告中。六桥的开发阶段冻结散列另见 `bridge-development-evidence.json`；其中临时路径仅为开发记录，最终可重放依据是本目录的源码及共享 fresh 验证，不依赖临时目录中的 olean。

重放命令使用已有固定依赖缓存，输出路径必须为新目录：

```sh
python3 scripts/formal/verify.py \
  --manifest drafts/public-proof-extractions-20261029/MG-P001/formal/manifest.json \
  --dependency-root /path/to/fixed-lean436-tauceti-dependencies \
  --lean /path/to/lean-4.36.0-rc1/bin/lean \
  --out /path/to/new-output
```

共享验证器只允许该profile的10个固定依赖包，并核对工具链和Git提交；不读取OET私有数学源码，也不复用本题源目录的编译产物。没有候选模型运行、commit或push。
