# MG-P002 公开来源与改编边界

来源 ID：`navier-stokes-estimate-alignment`。访问日期：2026-10-29。全部取材公开；没有使用未发布 OET 内容或私有数学材料。

## 已直接核对的来源

1. A. Bastounis、F. Circelli、A. C. Hansen，*Navier–Stokes lost in translation – Why Lean verification of AI autoformalisation does not guarantee correct natural language proofs*，arXiv:2610.08144v1，2026-10-06，[§3.1 与 §3.1.1](https://arxiv.org/html/2610.08144v1#S3.SS1)。本次作者直接阅读该固定 arXiv 版本的 Example 3.1、Remark 3.2 及算子、函数空间说明。
2. OpenAI，*Finite time blowup for Navier–Stokes*，[公开 PDF](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)，Lemma 8.6、式 (8.19)。本次检索到的 PDF 共 166 页，陈述在印刷页 95，证明起于印刷页 96；这与评论文对证明段落的页码引用一致。该 URL 未提供不可变版本号；这里记录访问日期与局部锚点，不声称已保存历史 PDF 快照。本次直接核对了相关陈述与证明段落，没有通读或认证整篇论文。
3. `openai/NavierStokesAndEuler`，[固定 commit `f9e8bc5b38b6e212696e8a30e3e91517af887bbd` 的 `NavierStokes/SmoothFamilyTorusInverse.lean`，行 1059–1080](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/SmoothFamilyTorusInverse.lean#L1059-L1080)。声明名 `norm_derivativeWord_inverse_le`。GitHub 文件接口返回的完整文件 blob SHA 为 `c607eb6f2460a3ba55dc2218072cd504bf6253bf`；本次按行读取了上述声明及证明。该 SHA 是 Git blob 身份，不是本地 Lean 编译证据。

## 核对到的数学事实

原辅助算子是二维周期环面上的 $N=(\sqrt2-1)\partial_{y_1}+\partial_{y_2}$，右端光滑且零 Haar 均值。原式 (8.19) 使用输入的 $C^{m+4}$ 范数控制输出的 $C^m$ 范数。它的局部证明用一次小除数增长以及二维三次幂衰减的可和性。

固定 Lean 声明针对一个长度为 $m$ 的导数词，假设函数值以及两个坐标方向的 $m+5$ 阶纯导数均受同一常数控制。证明中使用四次幂倒数的格点和。把对应的导数词结论合并可以取得五阶输入损失的 $C^m$ 控制；该特定声明本身没有写出原四阶输入估计。

这是所核对局部声明的强度差异。没有由此推断四阶估计不成立、其他文件无法证明它，或 Navier–Stokes 主定理错误。本题参考稿独立证明固定方向的四阶估计成立。

## 本题保留与更改

- 保留二维周期环面、归一化均值、复值光滑函数、零均值逆、原固定方向作为必须处理的特例，以及 $C^{m+4}\to C^m$ 的实际目标。
- 将固定方向推广为任意无理数 $\alpha$，要求分类光滑满射性和全部 Sobolev 损失。这是明确新增的数学问题，不是原论文命题的转录。
- 去掉原应用中的慢参数、径向与轴向支撑、坐标覆盖、物理场重建和 Navier–Stokes 方程；题目只研究固定环面上的独立标量算子。
- 新增明确的 Fourier/Sobolev 范数定义、一般方向的不可解构造、固定方向的尖锐 Sobolev 阈值。没有把四阶损失称为 $C^m$ 尺度的最优阶数。
- 采用 exploration 类别且候选只见 task.md；来源、真假、参考论证、评分和审核状态均不进入候选投影。没有提供一个抽象假设字段中已经含有目标结论的伪形式证书。

本题没有复制原论文的大段文本或外部 Lean 源文件，也没有声称运行过原模型、复现过模型失败或完成过本题 Lean 验证。静态数学内容已由作者自查，难度尚未校准，human pending。
