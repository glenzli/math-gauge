# 幂等分解在增厚逆系中的恢复

设 $I$ 是非空的有向偏序集，$S$ 及每个 $R_i$ 都是含幺交换环。给定逆系的含幺环同态
$$
\rho_{ij}:R_j\longrightarrow R_i\quad(i\le j),\qquad
\rho_{ii}=\mathrm{id},\quad \rho_{ij}\rho_{jk}=\rho_{ik},
$$
以及满射含幺环同态 $p_i:R_i\to S$，满足 $p_i\rho_{ij}=p_j$。对每个 $i$ 及每个 $r\in\ker p_i$，假设存在正整数 $n=n(i,r)$ 使 $r^n=0$。

令
$$
L=\left\{(r_i)\in\prod_{i\in I}R_i:\rho_{ij}(r_j)=r_i\text{ 对所有 }i\le j\right\}
$$
取分量环运算。对任意有限集合 $J$，记
$$
\mathcal D_J(R)=\left\{(e_j)\in R^J:
e_j^2=e_j,\ e_je_k=0\ (j\ne k),\ \sum_{j\in J}e_j=1\right\}.
$$

研究能否从这些数据得到一个与指标选择无关的含幺环同态 $p:L\to S$，并使其分量作用诱导双射
$$
\mathcal D_J(L)\longrightarrow\mathcal D_J(S)
$$
对所有有限 $J$ 都成立。对于相应的 $e\in\mathcal D_J(S)$ 与 $\widetilde e\in\mathcal D_J(L)$，还要求构造由商映射给出的环同构
$$
L\longrightarrow\prod_{j\in J}L/(1-\widetilde e_j)L.
$$

最后，对同一指标集上的另一组数据 $(R'_i,S',\rho'_{ij},p'_i)$，设给定含幺环同态 $u:S\to S'$、$u_i:R_i\to R'_i$，使
$$
u_i\rho_{ij}=\rho'_{ij}u_j,\qquad p'_iu_i=up_i.
$$
研究上述分解双射是否与这些同态诱导的映射相容，给出完整论证。
