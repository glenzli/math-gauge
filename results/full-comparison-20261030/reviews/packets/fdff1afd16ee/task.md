# 对称提升的逐层相容实现

设 $G$ 为有限群，$k$ 为域，$C$ 为有限维 $k$ 线性 $G$ 表示。对每个整数 $n\ge1$，给定有限维 $k$ 线性 $G$ 表示的短正合列

$$0\longrightarrow A_n\xrightarrow{i_n}B_n\xrightarrow{q_n}C\longrightarrow0,$$

其中 $i_n,q_n$ 均为 $G$ 等变映射。每一列都有 $G$ 等变的线性分裂，即存在 $u_n:C\to B_n$ 满足 $q_nu_n=I_C$。

给定 $G$ 等变线性映射 $\alpha_n:A_{n+1}\to A_n$ 和 $\beta_n:B_{n+1}\to B_n$，满足

$$\beta_ni_{n+1}=i_n\alpha_n,\qquad q_n\beta_n=q_{n+1}.$$

令

$$A_\infty=\{(a_n)\in\prod_{n\ge1}A_n:\alpha_n(a_{n+1})=a_n\},\qquad
B_\infty=\{(b_n)\in\prod_{n\ge1}B_n:\beta_n(b_{n+1})=b_n\},$$

赋予逐坐标的线性结构和 $G$ 作用；定义 $i_\infty((a_n))=(i_n(a_n))$ 和 $q_\infty((b_n))=q_1(b_1)$。

把逐层分裂组织成一族 $G$ 等变线性映射 $s_n:C\to B_n$，同时满足

$$q_ns_n=I_C,\qquad \beta_ns_{n+1}=s_n,$$

由此建立 $B_\infty\cong A_\infty\oplus C$ 的 $G$ 表示同构，使该同构将 $i_\infty$ 对应于第一直和项的包含、将 $q_\infty$ 对应于第二直和项的投影。刻画所有此类相容分裂的自由度，并说明它们在整塔的交换图同构下如何变换。请给出构造及完整论证。
