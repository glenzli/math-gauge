# 逐点有限轨道的规范分解

在 ZFC 中工作。设 $R$ 为任意含幺环，$M$ 为左 $R$-模，$T:M\to M$ 为 $R$-线性映射。对每个 $x\in M$，集合
\[
\{T^n x:n\in\mathbb N\}
\]
都是有限集，其中 $T^0=\mathrm{id}_M$。

定义
\[
N_T=\{x\in M:\exists n\in\mathbb N,\ T^n x=0\},\qquad
P_T=\{x\in M:\exists p\ge1,\ T^p x=x\}.
\]

研究是否存在唯一的 $R$-线性映射 $e_T:M\to M$，使每个 $x\in M$ 都满足
\[
e_Tx\in P_T,\qquad x-e_Tx\in N_T.
\]
若可以构造，建立由它给出的 $M\cong N_T\oplus P_T$、$e_T$ 的核与像、幂等性，以及 $T$ 在 $P_T$ 上的限制是否构成自同构。

还要求该构造与交织映射相容：若另一个左 $R$-模 $M'$ 上的 $T'$ 满足同样的逐点有限轨道条件，且 $a:M\to M'$ 为满足 $aT=T'a$ 的 $R$-线性映射，确定是否总有
\[
a e_T=e_{T'}a,
\]
并给出论证。
