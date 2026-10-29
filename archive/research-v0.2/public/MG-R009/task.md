# 局部记录的有效下降商

采用 ZFC，固定 Grothendieck 宇宙 $\mathcal U\in\mathcal V$，且 $\mathbb N\in\mathcal U$。令 $\operatorname{Prof}_{\mathcal U}$ 为底集属于 $\mathcal U$ 的 profinite 空间及连续映射组成的范畴；profinite 指紧、Hausdorff、全不连通。覆盖是有限个连续映射组成的联合满射族。

本题的 condensed set 是函子 $X:\operatorname{Prof}_{\mathcal U}^{\mathrm{op}}\to\mathbf{Set}_{\mathcal V}$，满足以下粘合条件：在任意覆盖上给定局部元素，若它们在两两纤维积上的限制相等，则它们来自唯一的全局元素。空空间的空覆盖也包含在内。对 $K\in\operatorname{Prof}_{\mathcal U}$，记 $h_K(U)=C(U,K)$，限制映射为预复合。

给定连续满射 $p:T\to S$，其中 $T,S\in\operatorname{Prof}_{\mathcal U}$。令 $R=T\times_S T$，投影为 $r_1,r_2:R\rightrightarrows T$。

为这一识别关系建立有效下降商：构造 condensed set $Q$ 及映射 $h_T\to Q$，使

$$h_R\rightrightarrows h_T\longrightarrow Q$$

是余等化图，并使 $h_R$ 通过所给投影与 $h_T\times_Qh_T$ 同构。建立该构造在任意 condensed set $X\to Q$ 下拉回的稳定性，并用相容局部记录解释其泛性质。请给出主定理、构造及完整论证。
