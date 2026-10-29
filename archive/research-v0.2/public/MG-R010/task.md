# 由紧全不连通探针重构空间

采用 ZFC，固定 Grothendieck 宇宙 $\mathcal U\in\mathcal V$，且 $\mathbb N\in\mathcal U$。本题的空间均为底集属于 $\mathcal U$ 的 Hausdorff 空间。令 $\operatorname{Prof}_{\mathcal U}$ 为其中的紧全不连通空间及连续映射组成的范畴。

一个空间 $X$ 的探针记录为反变函子

$$h_X:\operatorname{Prof}_{\mathcal U}^{\mathrm{op}}\longrightarrow\mathbf{Set}_{\mathcal V},
\qquad h_X(S)=C(S,X),$$

其中 $C(S,X)$ 表示连续映射的集合，限制映射为预复合。

建立由这些记录决定的空间重构。目标是在每个 $X$ 的同一底集上构造一个自然的 Hausdorff 拓扑 $X^\dagger$，使恒等映射 $X^\dagger\to X$ 连续、同一底集映射给出 $h_{X^\dagger}=h_X$，且再作一次重构保持拓扑不变。重构还应使所有 $X,Y$ 之间有自然双射

$$\operatorname{Nat}(h_X,h_Y)\cong C(X^\dagger,Y^\dagger),$$

并与恒等映射和复合相容。请给出主定理、构造及完整论证。
