# Fourier 逆、截断误差与参数边界

请按 S 编号逐项作答。所有阶段均必答；给出所要求的证明、构造或分类。判断命题时，给出结论及完整证明或满足全部前提的反例。援引前项或标准定理时说明实际适用条件。无需 Lean。



## S1 有限频带上的逆

在归一化环面 T² 上令 N_α=α∂_1+∂_2，α 无理。设 H_N 为仅含 0<|k|≤N 整频率的复三角多项式空间（N≥1）。构造 N_α 在 H_N 上的逆；对任意实 r 给出 H^r→H^r 逆范数精确式。

## S2 有算术界的截断误差

设 |αk_1+k_2|≥c⟨k⟩^{−s} 对全部 k≠0，c>0、s≥0。对光滑零均值 F 令 u_N 为 S1 中对频带截断 F_N 的解。构造光滑解 u，并对任意 r∈R、q≥0 证明 ||u−u_N||_{H^r}≤(2πc)^{-1}(1+N²)^{−q/2}||F||_{H^{r+s+q}}。

## S3 固定频带内改变方向

给两个无理方向 α,β，设其在 0<|k|≤N 上的小除数绝对值都至少 δ>0。对同一 F∈H_N，证明对应解满足 ||u_α−u_β||_{H^r}≤|α−β|N(2πδ²)^{-1}||F||_{H^r}。

## S4 整体对象与全部恢复目标

判定下面所列目标在给定条件下是否成立。若成立，完成全部构造、分类与性质的证明；若不成立，给出满足全部给定条件的反例。

令 $\mathbb T^2=\mathbb R^2/\mathbb Z^2$，配备归一化 Haar 测度，记

$$C^\infty_0(\mathbb T^2)=\left\{u\in C^\infty(\mathbb T^2;\mathbb C):\int_{\mathbb T^2}u=0\right\}.$$

对无理数 $\alpha\in\mathbb R\setminus\mathbb Q$，定义

$$N_\alpha u=\alpha\,\partial_{y_1}u+\partial_{y_2}u.$$

对 $k\in\mathbb Z^2$，令 $\langle k\rangle=(1+|k|^2)^{1/2}$，其中 $|k|$ 为 Euclidean 范数。对 $r\in\mathbb R$ 和光滑函数 $u$，采用范数

$$\|u\|_{H^r}^2=\sum_{k\in\mathbb Z^2}\langle k\rangle^{2r}|\widehat u(k)|^2,
\qquad
\widehat u(k)=\int_{\mathbb T^2}u(y)e^{-2\pi i k\cdot y}\,dy,$$

以及

$$\|u\|_{C^m}=\max_{a,b\ge0,\ a+b\le m}\sup_{y\in\mathbb T^2}|\partial_{y_1}^a\partial_{y_2}^b u(y)|
\qquad(m\in\mathbb N_0).$$

建立 $N_\alpha:C^\infty_0(\mathbb T^2)\to C^\infty_0(\mathbb T^2)$ 的可逆性与正则性理论：刻画哪些 $\alpha$ 使每个 $F\in C^\infty_0(\mathbb T^2)$ 都有唯一的光滑零均值解 $N_\alpha u=F$；同时确定全部 $s\ge0$，使对每个 $r\in\mathbb R$ 存在与 $u$ 无关的有限常数 $C_{\alpha,r,s}$，满足

$$\|u\|_{H^r}\le C_{\alpha,r,s}\|N_\alpha u\|_{H^{r+s}}
\qquad\text{对所有 }u\in C^\infty_0(\mathbb T^2).$$

在 $\alpha_* =\sqrt2-1$ 时，明确最小的允许损失 $s$ 及其是否取到，并判断是否对每个 $m\in\mathbb N_0$ 都存在与 $F$ 无关的有限常数 $C_m$，使零均值解满足

$$\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+4}}
\qquad(F\in C^\infty_0(\mathbb T^2)).$$

请给出完整的定理、构造与论证。

## S5 邻近方向的一致估计

令 α_*=√2−1。判定是否存在开区间 J∋α_*、有限 s≥0、C<∞，使每个无理 α∈J 及每个光滑零均值 u 都满足 ||u||_{L²}≤C||N_αu||_{H^s}。

## S6 一个具体方向的不可解数据

取 α=Σ_{n=1}^∞10^{−n!}。证明 α 无理，并构造一个光滑零均值 F 使 N_αu=F 没有光滑零均值解。要求给出同一个 F，而不是对每个估计分别给一个频率。
