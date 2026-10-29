# 多项式范数记录与谱恢复

设 $E\ne\{0\}$ 是复 Banach 空间，$T,T_n\in\mathcal B(E)$，$n\ge0$，满足

$$\|T\|\le1,\qquad\|T_n\|\le1,\qquad T_nx\longrightarrow Tx\quad(x\in E).$$

每个 $T_n$ 的像空间有限维。对复多项式 $p(z)=\sum_{k=0}^d a_kz^k$，采用

$$p(A)=\sum_{k=0}^d a_kA^k,\qquad A^0=I_E.$$

另已知，对每个这样的多项式都存在 $N_p$，使

$$\|p(T_n)\|=\|p(T)\|\qquad(n\ge N_p).$$

记 $\sigma(A)=\{\lambda\in\mathbb C:\lambda I_E-A\text{ 没有有界双侧逆}\}$。

为这套有限维像模型建立谱恢复定理。目标是证明：对每个 $\lambda\in\sigma(T)$，都能选取 $\lambda_n\in\sigma(T_n)$，使 $\lambda_n\to\lambda$。请给出恢复构造及完整论证。
