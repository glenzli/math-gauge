# 探针记录之间的映射空间

采用 ZFC，固定 Grothendieck 宇宙 $\mathcal U\in\mathcal V$，且 $\mathbb N\in\mathcal U$。本题的拓扑空间均为底集属于 $\mathcal U$ 的 Hausdorff 空间。令 $\operatorname{Prof}_{\mathcal U}$ 为其中的紧全不连通空间及连续映射组成的范畴。定义探针函子

$$h_X:\operatorname{Prof}_{\mathcal U}^{\mathrm{op}}\to\mathbf{Set}_{\mathcal V},
\qquad h_X(S)=C(S,X),$$

其中限制映射为预复合，函子的积逐测试对象计算。

对任意两个空间 $X,Y$，定义参数化映射记录

$$\mathcal H_{X,Y}(S)=\operatorname{Nat}(h_S\times h_X,h_Y).$$

若 $u:S'\to S$，其限制映射把 $\alpha$ 送到 $\alpha\circ(h_u\times I_{h_X})$。

为这些记录建立空间实现理论：构造 Hausdorff 空间 $M(X,Y)$ 以及在 $S$ 上自然的双射

$$C(S,M(X,Y))\cong\mathcal H_{X,Y}(S)
\qquad(S\in\operatorname{Prof}_{\mathcal U}).$$

构造还应给出求值自然变换 $\mathrm{ev}:h_{M(X,Y)}\times h_X\to h_Y$，使对于每个 Hausdorff 参数空间 $Z$，映射

$$\alpha\longmapsto\mathrm{ev}\circ(\alpha\times I_{h_X})$$

给出自然双射

$$\operatorname{Nat}(h_Z,h_{M(X,Y)})
\cong\operatorname{Nat}(h_Z\times h_X,h_Y),$$

并与参数变换及 $X,Y$ 中的连续映射相容。请确定实现空间的底集与拓扑，并给出主定理、构造及完整论证。
