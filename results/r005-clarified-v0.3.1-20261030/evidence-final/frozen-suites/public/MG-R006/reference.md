# 参考审核：逐层可解系统的兼容提升

原短正合目标为假。$B_n$ 的过渡满射和有限记录 $C_n$ 不能代替核塔 $A_n$ 中的相容修正条件。下面给出选择无关的障碍及完全显式反例。

## 总成立的左端与选择误差

逐分量检查可得

$$0\to\varprojlim A_n\to\varprojlim B_n\to\varprojlim C_n$$

正合：若兼容 $b_n$ 在每层落于核，则由 $\iota_n$ 单射唯一写成 $\iota_n(a_n)$；交换图迫使 $a_n$ 兼容。

定义群同态

$$\Delta_A:\prod_{n\ge1}A_n\to\prod_{n\ge1}A_n,
\quad (a_n)\mapsto(a_n-\alpha_n(a_{n+1})).$$

给定兼容 $c$，任选逐层提升 $b_n$。交换图保证 $b_n-\beta_n(b_{n+1})\in\ker\pi_n$，故唯一存在 $d_n\in A_n$ 使

$$\iota_n(d_n)=b_n-\beta_n(b_{n+1}).$$

若改选 $b'_n=b_n+\iota_n(a_n)$，则 $d'=d+\Delta_Aa$。因此

$$\delta(c)=[d]\in\operatorname{coker}\Delta_A$$

不依赖选择。对记录相加时可选择提升之和，故 $\delta$ 为同态；与塔的交换同态逐项计算，得自然性。

## 障碍的准确含义

$\delta(c)=0$ 当且仅当 $d=\Delta_Aa$ 对某个 $a$ 成立。此时改取 $b'_n=b_n-\iota_n(a_n)$，缺陷变为零，得到兼容提升。反之，已有兼容提升产生的缺陷为零，故类为零。因此它是某一记录可提升的必要充分条件。

一个兼容提升存在时，所有兼容提升构成 $\varprojlim A_n$ 的挠子：任意两解之差是唯一的兼容核元素，反过来加任何兼容核元素仍为解。这里没有额外选定一个规范原点。

题设 $\beta_n$ 满射还给出 $\Delta_B$ 满射。对任意 $u_n\in B_n$，先任取 $b_1$，再递归选 $b_{n+1}$ 使 $\beta_n(b_{n+1})=b_n-u_n$。于是 $\Delta_Bb=u$。

对任意 $d\in\prod A_n$，用这点解 $\Delta_Bb=(\iota_nd_n)_n$。则 $c_n=\pi_n(b_n)$ 兼容且 $\delta(c)=[d]$。所以本题真正自然的序列为

$$0\to\varprojlim A_n\to\varprojlim B_n\to\varprojlim C_n
\xrightarrow{\delta}\operatorname{coker}\Delta_A\to0.$$

这里给出了障碍群的具体商构造，不需要把高阶导出函子作为未经说明的额外对象。

## 有限记录仍不能整体提升

取

$$A_n=2^n\mathbb Z,\qquad B_n=\mathbb Z,\qquad C_n=\mathbb Z/2^n\mathbb Z,$$

行映射为包含与模映射。$\alpha_n$ 是包含，$\beta_n$ 为恒等，$\gamma_n$ 为自然约化。所有行短正合、所有 $C_n$ 有限、两类题设过渡满射，图表交换。

由于 $3$ 在模 $2^n$ 下可逆，令 $c_n$ 为满足 $3c_n=1$ 的唯一剩余类。唯一性保证它们相容。每一层以及每个有限前缀都能用一个整数提升：取最高层的任意整数代表即可。

若有兼容整体提升，由 $\beta_n=I$ 可知所有 $b_n$ 必为同一个整数 $b$。于是 $3b-1$ 被每个 $2^n$ 整除，故 $3b-1=0$，不可能。这给出一个具体不可提升记录；不只使用不可数性或模糊的“可能不正合”。

本例 $\varprojlim A_n=\bigcap_n2^n\mathbb Z=0$，$\varprojlim B_n=\mathbb Z$。核自由度为零也没有解决存在性。记录塔虽由有限集合组成，其可提升纤维不是非空有限集合塔，不能直接套用有限逆极限紧性去造整数解。

## 条件化修复

若额外要求所有 $\alpha_n$ 满射，和上面对 $\Delta_B$ 的递归证明完全相同，$\Delta_A$ 满射，障碍群消失，于是短正合结论成立。这个条件是充分的，不应冒充必要条件；对给定记录的精确判据仍为 $\delta(c)=0$，对本题整条序列的精确判据为 $\operatorname{coker}\Delta_A=0$。

## 来源与审核范围

背景核对：[Stacks 02N1](https://stacks.math.columbia.edu/tag/02N1)、[Stacks 07KV](https://stacks.math.columbia.edu/tag/07KV)。缺陷计算、四段正合序列和模 $2^n$ 见证在本稿完整展开。本轮保留同一数学目标与反例，定位为边界识别基线。AI 独立数学审核、人工审定、模型校准和形式化证据分别以本题 review.json 及其引用记录为准；可选的长障碍论证不改变短反例已完成主目标这一事实。
