以下给出题面（已完整读取自 [index.json](file:///private/tmp/math-gauge-neon-xhigh-20261119-v1/attempts/MG-GR021/physical-1/session/work/.visible-input/MG-GR021/index.json) 与 [01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v1/attempts/MG-GR021/physical-1/session/work/.visible-input/MG-GR021/01-user-001.txt)）全部三个目标的完整解答与严格证明。

---

## 零、预备定理与符号约定

### 0.1 援引的标准局部域定理及其适用条件

下文仅援引以下三项局部域（完备离散赋值域）的标准定理：

1. **Eisenstein 扩张与整数环定理**：设 $K$ 为完备离散赋值域，整数环为 $\mathcal O_K$，极大理想为 $\mathfrak p_K$；若首一多项式 $f(x)\in \mathcal O_K[x]$ 满足 Eisenstein 判别条件（除首项外各系数属于 $\mathfrak p_K$，常数项不属于 $\mathfrak p_K^2$），则 $f$ 在 $K$ 上不可约，其根 $\pi$ 生成的扩张 $L=K(\pi)$ 是次数为 $\deg f$ 的完全分歧扩张，且整数环为 $\mathcal O_L=\mathcal O_K[\pi]$，素元为 $\pi$。
2. **Hensel 引理（Newton 形式）**：设 $\mathcal O_K$ 为完备离散赋值环，$v$ 为其归一化赋值；若 $f(x)\in \mathcal O_K[x]$ 与 $a_0\in \mathcal O_K$ 满足 $v(f(a_0)) > 2v(f'(a_0))$，则存在唯一的 $a\in\mathcal O_K$ 满足 $f(a)=0$ 且 $v(a-a_0)\ge v(f(a_0))-v(f'(a_0))$。
   - **特例（$1+8\mathbb Z_2$ 开平方）**：对任意 $c\in 1+8\mathbb Z_2$，取 $f(x)=x^2-c\in\mathbb Z_2[x]$ 及 $a_0=1$。则 $v_2(f(1))=v_2(1-c)\ge 3 > 2 = 2v_2(2)=2v_2(f'(1))$，故存在唯一 $u\in 1+4\mathbb Z_2\subset 1+2\mathbb Z_2$ 使 $u^2=c$。
3. **局部域整数环的 $2$-进完备性与逆极限**：对 $F=\mathbb Q_2$ 的有限扩张 $L$，整数环 $\mathcal O_L$ 关于 $2$-进拓扑是分离完备的，即 $\bigcap_{M\ge 1} 2^M\mathcal O_L=\{0\}$ 且自然同态 $\mathcal O_L\xrightarrow{\sim}\varprojlim_{M\ge 1}\mathcal O_L/2^M\mathcal O_L$ 为同构；从而 $M_d(\mathcal O_L)\cong \varprojlim_M M_d(\mathcal O_L/2^M\mathcal O_L)$。

### 0.2 $K_\mu$ 的整数环与 Galois 作用

对 $\mu\in\{-1,2\}$：
- 当 $\mu=2$ 时，$x^2-2\in\mathbb Z_2[x]$ 为 Eisenstein 多项式，故 $K_2/\mathbb Q_2$ 是二次完全分歧扩张，整数环为 $\mathcal O_{K_2}=\mathbb Z_2[\theta_2]=\mathcal O_2$，素元为 $\pi_2:=\theta_2$，满足 $\pi_2^2=2$。
- 当 $\mu=-1$ 时，令 $\pi_{-1}:=1+\theta_{-1}$，其极小多项式 $(x-1)^2+1=x^2-2x+2\in\mathbb Z_2[x]$ 为 Eisenstein 多项式，故 $K_{-1}/\mathbb Q_2$ 也是二次完全分歧扩张，整数环为 $\mathcal O_{K_{-1}}=\mathbb Z_2[\pi_{-1}]=\mathbb Z_2[\theta_{-1}]=\mathcal O_{-1}$，素元为 $\pi_{-1}=1+\theta_{-1}$，满足 $\pi_{-1}^2=2\theta_{-1}$。

由此对 $L\in\{F,K_{-1},K_2\}$ 记
$$e_L:=[L:F]=\begin{cases}1,&L=F,\\2,&L=K_\mu,\end{cases}\qquad q_L:=|\mathcal O_L/2\mathcal O_L|=2^{e_L}.$$
特别地，$\mathcal O_\mu=\mathbb Z_2\oplus\mathbb Z_2\theta_\mu$ 是秩 $2$ 自由 $\mathbb Z_2$-模，因此对每个 $M\ge 1$：
- $2^M\mathcal O_\mu = 2^M\mathbb Z_2 \oplus 2^M\mathbb Z_2\theta_\mu$，$2^M\mathcal O_\mu \cap \mathbb Z_2 = 2^M\mathbb Z_2$，故自然映射 $\mathbb Z_2/2^M\mathbb Z_2\hookrightarrow \mathcal O_\mu/2^M\mathcal O_\mu$ 单射；
- 对 $x=a+b\theta_\mu\in\mathcal O_\mu$（$a,b\in\mathbb Z_2$），有 $\sigma_\mu(x)-x=-2b\theta_\mu$，故
  $$\sigma_\mu(x)\equiv x\pmod{2^M\mathcal O_\mu}\iff b\equiv 0\pmod{2^{M-1}\mathbb Z_2},$$
  $$\sigma_\mu(x)=x \iff b=0 \iff x\in\mathbb Z_2=\mathcal O_F.$$
特别地，若 $U\in\mathscr S_{K_\mu}(A)$ 满足 $\sigma_\mu(U)=U$，则 $U\in M_d(\mathbb Z_2)$ 且 $U-I_d\in 2M_d(\mathcal O_\mu)\cap M_d(\mathbb Z_2)=2M_d(\mathbb Z_2)$，从而 $\det U\equiv 1\pmod 2$ 即 $U\in\mathrm{GL}_d(\mathbb Z_2)$，因此
$$\mathscr S_{K_\mu}(A)^{\sigma_\mu}=\mathscr S_F(A).$$

### 0.3 组合与矩阵记号

固定块秩 $\mathbf n=(n_1,\ldots,n_r)$，$d=\sum_{i=1}^r n_i$，记
$$D:=\sum_{i=1}^r\binom{n_i}{2}=\frac12\sum_{i=1}^r n_i(n_i-1),\qquad S:=\sum_{i=1}^r\binom{n_i+1}{2}=D+d.$$
注意 $D=0 \iff n_1=\cdots=n_r=1 \iff \max_{1\le i\le r} n_i = 1$；而 $D>0 \iff \max_{1\le i\le r} n_i \ge 2$。

对任意交换环 $k$（特别地 $k=\mathbb F_2$ 或 $\mathcal O_L/2\mathcal O_L$），定义 $d\times d$ 分块对角对称矩阵与分块对角零对角对称（交替）矩阵空间：
$$\operatorname{Sym}_{\mathbf n}(k):=\bigl\{Z\in M_d(k):Z^{\mathsf T}=Z,\;[Z,E_j]=0\ (\forall j)\bigr\}=\bigoplus_{i=1}^r \operatorname{Sym}_{n_i}(k),$$
$$\operatorname{Alt}_{\mathbf n}(k):=\bigl\{Z\in \operatorname{Sym}_{\mathbf n}(k):Z_{aa}=0\ (\forall a=1,\ldots,d)\bigr\}=\bigoplus_{i=1}^r \operatorname{Alt}_{n_i}(k).$$
当 $k=\mathbb F_2$ 时，$|\operatorname{Sym}_{\mathbf n}(\mathbb F_2)|=2^{D+d}$，$|\operatorname{Alt}_{\mathbf n}(\mathbb F_2)|=2^D$；当 $k=\mathcal O_L/2\mathcal O_L$ 时，基数分别为 $q_L^{D+d}=2^{e_L(D+d)}$ 与 $q_L^D=2^{e_L D}$。

对每个合法输入 $A=(A_1,\ldots,A_r)$ 与每个 $i\in\{1,\ldots,r\}$，因 $A_i\equiv E_i\pmod 2$，对所有 $a\in I_i,b\notin I_i$ 有 $(A_i)_{ab}\in 2\mathbb Z_2$，定义可由 $A_i\bmod 4$ 有限计算的不变量
$$\tau_i(A):=\sum_{a\in I_i}\sum_{b\notin I_i}\frac{(A_i)_{ab}}{2}\pmod 2 \in \mathbb F_2,$$
即 $(A_i)_{I_i,I_i^c}$ 中模 $4$ 余 $2$ 的条目个数的奇偶性（当 $r=1$ 时为空和 $\tau_1(A)=0$）。

最后，对单块大小 $n\ge 1$ 与 $M\ge 2$，记标准正交同余子群及其模 $2^M\mathcal O_L$ 对应集合：
$$\Gamma_n(L):=\{W\in M_n(\mathcal O_L):W\equiv I_n\pmod{2\mathcal O_L},\;W^{\mathsf T}W=I_n\},$$
$$\Gamma_{n,M}^{\mathscr C}(L):=\{\bar W\in M_n(\mathcal O_L/2^M\mathcal O_L):\bar W\equiv I_n\pmod{2\mathcal O_L},\;\bar W^{\mathsf T}\bar W=I_n\},$$
$$\Gamma_{n,M}^{\mathscr R}(L):=\{W\bmod 2^M\mathcal O_L:W\in \Gamma_n(L)\}\subseteq \Gamma_{n,M}^{\mathscr C}(L).$$
（注：满足 $W\equiv I_n\pmod{2R}$ 的矩阵必有 $\det W\equiv 1\pmod{2R}$，从而自动可逆。）

---

## 一、核心结构约化与第 1 题完整解答

### 1.1 典范对称正交幂等投影与分块解耦

**引理 1.1（典范幂等投影 $P_1,\ldots,P_r$ 与块 Gram 矩阵）**  
对任意合法输入 $A_1,\ldots,A_r\in M_d(\mathbb Z_2)$，存在唯一一组矩阵 $P_1,\ldots,P_r\in M_d(\mathbb Z_2)$ 满足：
1. 每个 $P_i$ 属于 $\mathbb Z_2[A_i]$ 的 $2$-进闭包，且对任意 $M\ge 1$ 存在整系数多项式 $f_M\in\mathbb Z[x]$ 使 $P_i\equiv f_M(A_i)\pmod{2^M M_d(\mathbb Z_2)}$；
2. $P_i^{\mathsf T}=P_i$，$P_i^2=P_i$，$P_i\equiv E_i\pmod 2$，$P_i A_j=A_j P_i$（$\forall i,j$），$P_i P_j=\delta_{ij} P_i$，以及 $\sum_{i=1}^r P_i=I_d$；
3. 记 $G_i:=(P_i)_{I_i,I_i}\in M_{n_i}(\mathbb Z_2)$，则 $G_i$ 对称且存在对称矩阵 $H_i\in M_{n_i}(\mathbb Z_2)$ 使 $G_i=I_{n_i}+4H_i$，且
   $$\operatorname{tr}(H_i)\equiv \tau_i(A)\pmod 2,\qquad \det(G_i)\equiv 1+4\tau_i(A)\pmod 8.$$

**证明**：  
对每个 $i$，定义迭代序列 $X_{i,0}:=A_i$，$X_{i,k+1}:=3X_{i,k}^2-2X_{i,k}^3$（$k\ge 0$）。在交换环 $\mathbb Z_2[A_i]$ 中有恒等式
$$X_{i,k+1}-X_{i,k}=(1-2X_{i,k})(X_{i,k}^2-X_{i,k}),\qquad X_{i,k+1}^2-X_{i,k+1}=(X_{i,k}^2-X_{i,k})^2(4X_{i,k}^2-4X_{i,k}-3).$$
由 $A_i\equiv E_i\pmod 2$ 及 $E_i^2=E_i$ 得 $X_{i,0}^2-X_{i,0}\in 2M_d(\mathbb Z_2)$。对 $k$ 归纳立得
$$X_{i,k}^2-X_{i,k}\in 2^{2^k}M_d(\mathbb Z_2),\qquad X_{i,k+1}-X_{i,k}\in 2^{2^k}M_d(\mathbb Z_2).$$
由 $M_d(\mathbb Z_2)$ 的完备性，极限 $P_i:=\lim_{k\to\infty} X_{i,k}\in M_d(\mathbb Z_2)$ 存在，且对 $2^k\ge M$ 有 $P_i\equiv X_{i,k}\pmod{2^M M_d(\mathbb Z_2)}$，这给出 (1)。

由于 $A_i^{\mathsf T}=A_i$、$A_iA_j=A_jA_i$，每个 $X_{i,k}$ 对称且与所有 $A_j,X_{j,\ell}$ 交换，取极限得 $P_i^{\mathsf T}=P_i$、$P_i^2=P_i$、$P_i\equiv X_{i,0}\equiv E_i\pmod 2$、$P_iA_j=A_jP_i$、$P_iP_j=P_jP_i$。若 $i\ne j$，记 $Q:=P_iP_j$，则 $Q^2=Q$ 且 $Q\equiv E_iE_j=0\pmod 2$，于是 $Q(I_d-Q)=0$；因 $I_d-Q\equiv I_d\pmod 2$ 在 $M_d(\mathbb Z_2)$ 中可逆，故 $P_iP_j=0$。类似地，$S:=\sum_i P_i$ 为幂等矩阵且 $S\equiv \sum_i E_i=I_d\pmod 2$ 可逆，由 $(I_d-S)S=0$ 得 $\sum_i P_i=I_d$，这给出 (2)。（唯一性：若 $P_i'$ 也满足 $P_i'^2=P_i'$、$P_i'P_i=P_iP_i'$ 与 $P_i'\equiv E_i\pmod 2$，令 $D_i=P_i'-P_i\in 2M_d(\mathbb Z_2)$，则 $D_i^3=D_i$ 即 $D_i(I_d-D_i^2)=0$，而 $I_d-D_i^2$ 可逆，故 $P_i'=P_i$。）

现证 (3)。由 $X_{i,k+1}-X_{i,k}\in 2^{2^k}M_d(\mathbb Z_2)$（$k\ge 1$），有 $P_i\equiv X_{i,1}=3A_i^2-2A_i^3\pmod{4M_d(\mathbb Z_2)}$。写 $A_i=E_i+2B_i$（$B_i\in M_d(\mathbb Z_2)$ 对称），则
$$A_i^2\equiv E_i+2(E_iB_i+B_iE_i)\pmod 4,\qquad 2A_i^3\equiv 2E_i\pmod 4,$$
从而
$$P_i\equiv 3E_i+6(E_iB_i+B_iE_i)-2E_i\equiv E_i+2(E_iB_i+B_iE_i)\pmod 4.$$
特别地，对 $a\in I_i,b\notin I_i$，$(E_iB_i+B_iE_i)_{ab}=(B_i)_{ab}=\frac12(A_i)_{ab}$，于是 $(P_i)_{ab}\equiv (A_i)_{ab}\pmod 4$。令 $Y_i:=\frac12(P_i)_{I_i,I_i^c}\in M_{n_i\times(d-n_i)}(\mathbb Z_2)$，则 $(Y_i)_{ab}\equiv \frac12(A_i)_{ab}\pmod 2$。因 $P_i$ 对称且幂等，取 $P_i^2=P_i$ 的 $(I_i,I_i)$ 块得
$$G_i^2+4Y_iY_i^{\mathsf T}=G_i \implies G_i(I_{n_i}-G_i)=4Y_iY_i^{\mathsf T}.$$
由于 $G_i\equiv I_{n_i}\pmod 2$ 在 $M_{n_i}(\mathbb Z_2)$ 中可逆，故 $I_{n_i}-G_i=4G_i^{-1}Y_iY_i^{\mathsf T}\in 4M_{n_i}(\mathbb Z_2)$，于是 $G_i\equiv I_{n_i}\pmod 4$、$G_i^{-1}\equiv I_{n_i}\pmod 4$，从而
$$G_i = I_{n_i}-4G_i^{-1}Y_iY_i^{\mathsf T}\equiv I_{n_i}+4Y_iY_i^{\mathsf T}\pmod 8.$$
写 $G_i=I_{n_i}+4H_i$（$H_i^{\mathsf T}=H_i\in M_{n_i}(\mathbb Z_2)$），则 $H_i\equiv Y_iY_i^{\mathsf T}\pmod 2$，因此
$$\operatorname{tr}(H_i)\equiv \operatorname{tr}(Y_iY_i^{\mathsf T})=\sum_{a\in I_i}\sum_{b\notin I_i}(Y_i)_{ab}^2\equiv \sum_{a\in I_i}\sum_{b\notin I_i}\frac{(A_i)_{ab}}{2}=\tau_i(A)\pmod 2.$$
最后由行列式的 Leibniz 展开，任意非恒等置换的项至少含两个非对角元 $4(H_i)_{ab}$，故被 $16$ 整除，从而
$$\det(G_i)=\det(I_{n_i}+4H_i)\equiv \prod_{a=1}^{n_i}(1+4(H_i)_{aa})\equiv 1+4\operatorname{tr}(H_i)\equiv 1+4\tau_i(A)\pmod 8.\qquad\square$$

**引理 1.2（条件等价性与分块解耦）**  
设 $L\in\{F,K_{-1},K_2\}$，$R\in\{\mathcal O_L,\mathcal O_L/2^M\mathcal O_L\}$（$M\ge 2$）。
1. 对任意满足 $U\equiv I_d\pmod{2R}$ 与 $U^{\mathsf T}U=I_d$ 的 $U\in\mathrm{GL}_d(R)$，有
   $$[U^{\mathsf T}A_iU,E_j]=0\ (\forall i,j) \iff U^{\mathsf T}P_iU=E_i\ (\forall i).$$
2. 令 $T:=\sum_{i=1}^r P_iE_i\in M_d(\mathbb Z_2)$。则 $T\equiv I_d\pmod 2$（故 $T\in\mathrm{GL}_d(\mathbb Z_2)$），$P_iT=TE_i$（$\forall i$），且 $T^{\mathsf T}T=G:=\operatorname{diag}(G_1,\ldots,G_r)$。映射 $U\mapsto V:=T^{-1}U=\operatorname{diag}(V_1,\ldots,V_r)$ 诱导了 $\sigma_\mu$-等变且与模 $2^M\mathcal O_L$ 约化相容的双射：
   $$\mathscr S_L(A)\xrightarrow{\;\sim\;}\prod_{i=1}^r \mathscr S_L^{(i)},\qquad \mathscr C_{L,M}(A)\xrightarrow{\;\sim\;}\prod_{i=1}^r \mathscr C_{L,M}^{(i)},\qquad \mathscr R_{L,M}(A)\xrightarrow{\;\sim\;}\prod_{i=1}^r \mathscr R_{L,M}^{(i)},$$
   其中
   $$\mathscr S_L^{(i)}:=\bigl\{V_i\in M_{n_i}(\mathcal O_L):V_i\equiv I_{n_i}\pmod{2\mathcal O_L},\; V_i^{\mathsf T}G_iV_i=I_{n_i}\bigr\},$$
   $\mathscr C_{L,M}^{(i)}$ 是模 $2^M\mathcal O_L$ 对应的有限集合，$\mathscr R_{L,M}^{(i)}$ 是 $\mathscr S_L^{(i)}$ 模 $2^M\mathcal O_L$ 的像。此外，因 $G_i\equiv I_{n_i}\pmod 4$，恒有 $\mathscr C_{L,2}^{(i)}=\Gamma_{n_i,2}^{\mathscr C}(L)$。

**证明**：  
(1) 若 $[U^{\mathsf T}A_iU,E_j]=0$（$\forall i,j$）：当 $R=\mathcal O_L/2^M\mathcal O_L$ 时，由引理 1.1(1)，$P_i$ 在 $M_d(R)$ 中是 $A_i$ 的多项式 $f_M(A_i)$；因 $U^{\mathsf T}=U^{-1}$，故 $Q_i:=U^{\mathsf T}P_iU=f_M(U^{\mathsf T}A_iU)$ 与所有 $E_j$ 交换。当 $R=\mathcal O_L$ 时，对所有 $M\ge 1$ 模 $2^M\mathcal O_L$ 成立，由 $\bigcap_M 2^M\mathcal O_L=\{0\}$ 知 $Q_i=U^{\mathsf T}P_iU$ 与所有 $E_j$ 交换。又 $Q_i^2=Q_i$、$Q_i\equiv I_dE_iI_d=E_i\pmod{2R}$，令 $D_i:=Q_i-E_i\in 2M_d(R)$。由 $Q_i,E_i$ 为可交换幂等元得 $D_i^3=Q_i^3-3Q_i^2E_i+3Q_iE_i^2-E_i^3=Q_i-E_i=D_i$，即 $D_i(I_d-D_i^2)=0$。在 $M_d(R)$ 中，$D_i^2\in 4M_d(R)$ 幂零（当 $R=\mathcal O_L/2^M\mathcal O_L$）或几何级数 $\sum_{m\ge 0}D_i^{2m}$ 收敛（当 $R=\mathcal O_L$），故 $I_d-D_i^2$ 可逆，从而 $D_i=0$，即 $U^{\mathsf T}P_iU=E_i$。

反之，若 $U^{\mathsf T}P_jU=E_j$（$\forall j$），利用 $U^{\mathsf T}=U^{-1}$ 与 $[A_i,P_j]=0$ 得
$$[U^{\mathsf T}A_iU,E_j]=[U^{\mathsf T}A_iU,U^{\mathsf T}P_jU]=U^{\mathsf T}[A_i,P_j]U=0.$$

(2) $T=\sum_i P_iE_i\equiv \sum_i E_i^2=I_d\pmod 2$，故 $T\in\mathrm{GL}_d(\mathbb Z_2)$ 且 $T^{-1}\equiv I_d\pmod 2$。由 $P_iP_j=\delta_{ij}P_i$ 与 $E_iE_j=\delta_{ij}E_i$ 得
$$P_iT=P_iE_i=TE_i,\qquad T^{\mathsf T}T=\sum_{i,j}E_iP_iP_jE_j=\sum_{i=1}^r E_iP_iE_i=\operatorname{diag}(G_1,\ldots,G_r)=G.$$
令 $U=TV$（$V\in\mathrm{GL}_d(R)$）。则 $U\equiv I_d\pmod{2R}\iff V\equiv I_d\pmod{2R}$，且 $U^{\mathsf T}U=I_d\iff V^{\mathsf T}GV=I_d$。在此条件下，$U^{\mathsf T}P_iU=E_i\iff P_iU=UE_i\iff P_iTV=TVE_i\iff TE_iV=TVE_i\iff E_iV=VE_i$（$\forall i$），即 $V=\operatorname{diag}(V_1,\ldots,V_r)$ 为分块对角阵，且 $V^{\mathsf T}GV=I_d\iff V_i^{\mathsf T}G_iV_i=I_{n_i}$（$\forall i$）。因 $T\in\mathrm{GL}_d(\mathbb Z_2)$ 满足 $\sigma_\mu(T)=T$，该对应 $\sigma_\mu$-等变且与约化相容。最后，由 $G_i\equiv I_{n_i}\pmod 4$ 立知 $M=2$ 时 $\mathscr C_{L,2}^{(i)}=\Gamma_{n_i,2}^{\mathscr C}(L)$。$\square$

---

### 1.2 第 1 题结论与证明

#### 定理 1.1（可行性判准与空集例子）

对任意合法输入 $A=(A_1,\ldots,A_r)$ 和任意 $L\in\{F,K_{-1},K_2\}$：
$$\mathscr S_L(A)\ne\emptyset \iff \tau_i(A)=0\quad(\forall i=1,\ldots,r) \iff \mathscr S_F(A)\ne\emptyset.$$
该判准与扩域 $L\in\{F,K_{-1},K_2\}$ 无关，且仅依赖 $A_i\bmod 4$ 的有限计算。进一步：
- 当 $r=1$ 时，$\tau_1(A)=0$ 恒成立，故 $\mathscr S_L(A)$ 永非空；
- 当 $r\ge 2$ 时，存在合法 $A$ 使 $\mathscr S_L(A)=\emptyset$。

**证明**：  
**必要性（同时证明当 $M\ge 3$ 且 $\mathscr C_{L,M}(A)\ne\emptyset$ 时必有 $\tau_i(A)=0$）**：  
设对某个 $M\ge 3$ 有 $\mathscr C_{L,M}(A)\ne\emptyset$（当 $\mathscr S_L(A)\ne\emptyset$ 时自然成立）。由引理 1.2，每个 $i$ 存在 $V_i\in M_{n_i}(\mathcal O_L)$ 满足 $V_i\equiv I_{n_i}\pmod{2\mathcal O_L}$ 与 $V_i^{\mathsf T}G_iV_i\equiv I_{n_i}\pmod{2^M\mathcal O_L}$。取行列式并模 $8\mathcal O_L$（因 $M\ge 3$）：
$$\det(V_i)^2\det(G_i)\equiv 1\pmod{8\mathcal O_L}.$$
因 $V_i\equiv I_{n_i}\pmod{2\mathcal O_L}$，写 $\det(V_i)=1+2t$（$t\in\mathcal O_L$），则 $\det(V_i)^2=1+4(t+t^2)$。由引理 1.1(3)，$\det(G_i)^{-1}\equiv \det(G_i)\equiv 1+4\tau_i(A)\pmod 8$，于是
$$t+t^2\equiv \tau_i(A)\pmod{2\mathcal O_L}.$$
- 若 $L=F$：$t\in\mathbb Z_2$ 恒有 $t+t^2=t(t+1)\equiv 0\pmod 2$，故 $\tau_i(A)=0$。
- 若 $L=K_\mu$：写 $t=u+v\theta_\mu$（$u,v\in\mathbb Z_2$），则
  $$t+t^2=(u+u^2+\mu v^2)+(v+2uv)\theta_\mu\equiv \mu v^2+v\theta_\mu\pmod{2\mathcal O_\mu}.$$
  在 $\mathcal O_\mu/2\mathcal O_\mu=\mathbb F_2\oplus\mathbb F_2\theta_\mu$ 中比较 $\theta_\mu$-系数得 $v\equiv 0\pmod 2$，再比较 $1$-系数得 $\tau_i(A)\equiv \mu v^2\equiv 0\pmod 2$。

**充分性**：设 $\tau_i(A)=0$（$\forall i$）。固定 $i$，记 $n=n_i$，$G=G_i=I_n+4H$，则 $H^{\mathsf T}=H\in M_n(\mathbb Z_2)$ 且 $\operatorname{tr}(H)\equiv 0\pmod 2$。下面构造 $V_i\in\mathscr S_F^{(i)}$：
1. **模 $4$ 合同对角化**：对 $n$ 归纳证明存在 $L_0\in\mathrm{GL}_n(\mathbb Z_2)$ 满足 $L_0\equiv I_n\pmod 4$ 且 $L_0^{\mathsf T}GL_0=\operatorname{diag}(d_1,\ldots,d_n)$，$d_a\equiv G_{aa}\pmod 8$。$n=1$ 时取 $L_0=(1)$；若 $n\ge 2$，分块写 $G=\begin{pmatrix}g_{11}&4v^{\mathsf T}\\4v&\widetilde G\end{pmatrix}$（$g_{11}\in 1+4\mathbb Z_2\subset\mathbb Z_2^\times$），令 $E:=\begin{pmatrix}1&-4g_{11}^{-1}v^{\mathsf T}\\0&I_{n-1}\end{pmatrix}\equiv I_n\pmod 4$，则 $E^{\mathsf T}GE=\operatorname{diag}(g_{11},\widetilde G-16g_{11}^{-1}vv^{\mathsf T})$，其右下块对称且模 $16$ 同余于 $\widetilde G$，施以归纳假设即得 $L_0$。
2. **归一化为 $1$ 与偶数个 $5$**：因 $d_a\equiv G_{aa}=1+4H_{aa}\pmod 8$，故 $d_a\equiv 5\pmod 8 \iff H_{aa}\equiv 1\pmod 2$，而其余 $d_a\equiv 1\pmod 8$。于是满足 $d_a\equiv 5\pmod 8$ 的下标个数 $k$ 满足 $k\equiv \sum_{a=1}^n H_{aa}=\operatorname{tr}(H)\equiv 0\pmod 2$，即 $k$ 为偶数。
   - 若 $d_a\equiv 1\pmod 8$，则 $d_a^{-1}\in 1+8\mathbb Z_2$，由 Hensel 引理（第 0.1 节特例）取 $u_a\in 1+4\mathbb Z_2$ 使 $u_a^2 d_a=1$；
   - 若 $d_a\equiv 5\pmod 8$，则 $5d_a^{-1}\in 1+8\mathbb Z_2$，同样由 Hensel 引理取 $u_a\in 1+4\mathbb Z_2$ 使 $u_a^2 d_a=5$。
   令 $D_u:=\operatorname{diag}(u_1,\ldots,u_n)\equiv I_n\pmod 4$，则 $(L_0D_u)^{\mathsf T}G(L_0D_u)$ 是对角元仅含 $1$ 和偶数个 $5$ 的对角阵。
3. **成对消去 $5$**：将 $k$ 个取值为 $5$ 的坐标两两配对。对每一对，矩阵
   $$M_0:=\frac15\begin{pmatrix}1&-2\\2&1\end{pmatrix}\in\mathrm{GL}_2(\mathbb Z_2)$$
   满足 $M_0\equiv I_2\pmod 2$ 且 $M_0^{\mathsf T}(5I_2)M_0=I_2$。在每一对坐标上放置 $M_0$、在其余坐标上放置 $1$ 得到矩阵 $Q\in\mathrm{GL}_n(\mathbb Z_2)$，满足 $Q\equiv I_n\pmod 2$。置 $V_i:=L_0D_uQ$，则 $V_i\equiv I_n\pmod 2$ 且 $V_i^{\mathsf T}G_iV_i=I_{n_i}$，即 $V_i\in\mathscr S_F^{(i)}$。

由引理 1.2，$U_0:=T\operatorname{diag}(V_1,\ldots,V_r)\in\mathscr S_F(A)\subseteq \mathscr S_L(A)$，从而 $\mathscr S_L(A)\ne\emptyset$。

**空集实际例子（对任意 $r\ge 2$ 与任意块秩 $n_1,\ldots,n_r\ge 1$）**：  
取 $p\in I_1,q\in I_2$（如 $p=1,q=n_1+1$），令 $S_{pq}:=e_pe_q^{\mathsf T}+e_qe_p^{\mathsf T}$，置
$$A_1:=E_1+2S_{pq},\qquad A_2:=E_2-2S_{pq},\qquad A_i:=E_i\quad(3\le i\le r).$$
显然 $A_i^{\mathsf T}=A_i$、$A_i\equiv E_i\pmod 2$；因 $A_1+A_2=E_1+E_2$ 在 $I_1\cup I_2$ 上为恒等而在其补上为零，故 $A_1(E_1+E_2)=A_1=(E_1+E_2)A_1$，从而 $A_1A_2=A_1(E_1+E_2-A_1)=A_1-A_1^2=A_2A_1$，且 $i\ge 3$ 时 $A_i$ 与 $A_1,A_2$ 支集不交，故所有 $A_i$ 两两可交换，是合法输入。此时 $\tau_1(A)=\tau_2(A)=1$，故对全部 $L\in\{F,K_{-1},K_2\}$ 有 $\mathscr S_L(A)=\emptyset$（且 $\mathscr R_{L,M}(A)=\emptyset$ 对所有 $M\ge 2$，$\mathscr C_{L,M}(A)=\emptyset$ 对所有 $M\ge 3$）。与此同时，令 $\bar U:=I_d+2S_{pq}\bmod 4\mathcal O_L$：由于 $S_{pq}E_1+E_1S_{pq}=S_{pq}$，直接计算得 $U^{\mathsf T}U\equiv I_d\pmod 4$ 且 $U^{\mathsf T}A_iU\equiv E_i\pmod 4$（$\forall i$），故 $\bar U\in\mathscr C_{L,2}(A)\ne\emptyset$。$\square$

**推论 1.1（基点扭子同构）**  
每当 $\mathscr S_F(A)\ne\emptyset$（即 $\forall i,\;\tau_i(A)=0$），任取基点 $U_0\in\mathscr S_F(A)$，映射 $W=\operatorname{diag}(W_1,\ldots,W_r)\mapsto U=U_0W$ 给出 $\sigma_\mu$-等变、约化相容且保持模任意 $2^N\mathcal O_\mu$ 同余的双射：
$$\prod_{i=1}^r \Gamma_{n_i}(L)\xrightarrow{\;\sim\;}\mathscr S_L(A),\qquad \prod_{i=1}^r \Gamma_{n_i,M}^{\mathscr C}(L)\xrightarrow{\;\sim\;}\mathscr C_{L,M}(A),\qquad \prod_{i=1}^r \Gamma_{n_i,M}^{\mathscr R}(L)\xrightarrow{\;\sim\;}\mathscr R_{L,M}(A).$$

**证明**：因 $U_0\in\mathrm{GL}_d(\mathbb Z_2)$ 满足 $\sigma_\mu(U_0)=U_0$、$U_0\equiv I_d\pmod 2$、$U_0^{\mathsf T}U_0=I_d$ 与 $U_0^{\mathsf T}P_iU_0=E_i$，对 $U=U_0W$（$W\in\mathrm{GL}_d(R)$，$R\in\{\mathcal O_L,\mathcal O_L/2^M\mathcal O_L\}$）有：$U\equiv I_d\pmod{2R}\iff W\equiv I_d\pmod{2R}$；$U^{\mathsf T}U=I_d\iff W^{\mathsf T}W=I_d$；在此下由引理 1.2(1)，$[U^{\mathsf T}A_iU,E_j]=0\ (\forall i,j)\iff W^{\mathsf T}E_iW=E_i\ (\forall i)\iff W=\operatorname{diag}(W_1,\ldots,W_r)$。$\square$

---

#### 定理 1.2（$\bar U\in\mathscr C_{L,M}(A)$ 属于 $\mathscr R_{L,M}(A)$ 的可核验充要条件）

设 $L\in\{F,K_{-1},K_2\}$，$M\ge 2$，对任意合法输入 $A$ 与任意 $\bar U\in\mathscr C_{L,M}(A)$，任取 $\bar U$ 在 $M_d(\mathcal O_L)$（或 $M_d(\mathcal O_L/2^{M+1}\mathcal O_L)$）中的提升 $U$，则：
$$\bar U\in\mathscr R_{L,M}(A) \iff \operatorname{diag}(U^{\mathsf T}U-I_d)\equiv 0\pmod{2^{M+1}\mathcal O_L},$$
即对每一列 $a=1,\ldots,d$，列平方和满足
$$\sum_{b=1}^d U_{ba}^2 \equiv 1\pmod{2^{M+1}\mathcal O_L}.$$
该条件与提升 $U$ 的选取无关，可直接由 $\bar U$ 有限核验。

**证明**：  
**良定性**：对任意 $x,y\in\mathcal O_L$，因 $M\ge 2$（故 $2M\ge M+2>M+1$），有 $(x+2^My)^2=x^2+2^{M+1}xy+2^{2M}y^2\equiv x^2\pmod{2^{M+1}\mathcal O_L}$。从而 $\sum_{b=1}^d U_{ba}^2\bmod 2^{M+1}\mathcal O_L$ 仅依赖于 $\bar U$。

**必要性**：若 $\bar U\in\mathscr R_{L,M}(A)$，取真正解提升 $\widetilde U\in\mathscr S_L(A)$，则 $\widetilde U^{\mathsf T}\widetilde U=I_d$，由良定性即得 $\operatorname{diag}(U^{\mathsf T}U-I_d)\equiv 0\pmod{2^{M+1}\mathcal O_L}$。

**充分性**：设 $\bar U\in\mathscr C_{L,M}(A)$ 满足 $\operatorname{diag}(U^{\mathsf T}U-I_d)\equiv 0\pmod{2^{M+1}\mathcal O_L}$。

*第一步：证明 $\tau_i(A)=0$（$\forall i$），故 $\mathscr S_F(A)\ne\emptyset$。*  
若 $M\ge 3$，已由定理 1.1 必要性证明直接得到 $\tau_i(A)=0$（$\forall i$）。若 $M=2$，令 $V:=T^{-1}U\in M_d(\mathcal O_L)$。由引理 1.2，将 $V$ 分解为分块对角部分与非分块对角部分 $V=V_{\mathrm{diag}}+4V_{\mathrm{off}}$，其中 $V_{\mathrm{diag}}=\operatorname{diag}(V_1,\ldots,V_r)$ 满足 $V_i\equiv I_{n_i}\pmod{2\mathcal O_L}$ 且 $V_i^{\mathsf T}V_i\equiv I_{n_i}\pmod{4\mathcal O_L}$，$V_{\mathrm{off}}$ 的对角块全为零。因 $T^{\mathsf T}T=G$ 分块对角，
$$U^{\mathsf T}U=V^{\mathsf T}GV=V_{\mathrm{diag}}^{\mathsf T}GV_{\mathrm{diag}}+4\bigl(V_{\mathrm{diag}}^{\mathsf T}GV_{\mathrm{off}}+V_{\mathrm{off}}^{\mathsf T}GV_{\mathrm{diag}}\bigr)+16V_{\mathrm{off}}^{\mathsf T}GV_{\mathrm{off}}.$$
中间项的对角块为零，末项被 $16$ 整除，故对每个 $i$ 及每个 $a\in I_i$，$(V_i^{\mathsf T}G_iV_i-I_{n_i})_{aa}\equiv (U^{\mathsf T}U-I_d)_{aa}\equiv 0\pmod{8\mathcal O_L}$。写 $V_i=I_{n_i}+2X_i$（$X_i\in M_{n_i}(\mathcal O_L)$），由 $V_i^{\mathsf T}V_i\equiv I_{n_i}\pmod{4\mathcal O_L}$ 得 $X_i^{\mathsf T}\equiv X_i\pmod{2\mathcal O_L}$。结合 $G_i=I_{n_i}+4H_i$ 展开得
$$(V_i^{\mathsf T}G_iV_i-I_{n_i})_{aa}\equiv 4\biggl((X_i)_{aa}+(X_i)_{aa}^2+\sum_{b\ne a}(X_i)_{ba}^2+(H_i)_{aa}\biggr)\pmod{8\mathcal O_L}.$$
除以 $4$ 并对 $a=1,\ldots,n_i$ 求和：由于 $(X_i)_{ba}\equiv (X_i)_{ab}\pmod{2\mathcal O_L}$，成对合并 $(a,b)$ 与 $(b,a)$ 得 $(X_i)_{ba}^2+(X_i)_{ab}^2\equiv 2(X_i)_{ab}^2\equiv 0\pmod{2\mathcal O_L}$，故
$$\sum_{a=1}^{n_i}\bigl((X_i)_{aa}+(X_i)_{aa}^2\bigr)+\operatorname{tr}(H_i)\equiv 0\pmod{2\mathcal O_L}.$$
若 $L=F$，每项 $x+x^2\equiv 0\pmod 2$，得 $\operatorname{tr}(H_i)\equiv 0\pmod 2$；若 $L=K_\mu$，写 $(X_i)_{aa}=u_a+v_a\theta_\mu$（$u_a,v_a\in\mathbb Z_2$），则上式模 $2\mathcal O_\mu$ 为 $\mu\sum_a v_a^2 + (\sum_a v_a)\theta_\mu + \operatorname{tr}(H_i)\equiv 0\pmod{2\mathcal O_\mu}$。比较 $\theta_\mu$-系数得 $\sum_a v_a\equiv 0\pmod 2$，从而 $\sum_a v_a^2\equiv \sum_a v_a\equiv 0\pmod 2$，再比较 $1$-系数即得 $\tau_i(A)\equiv \operatorname{tr}(H_i)\equiv 0\pmod 2$。

*第二步：单块 Hensel 提升引理。*  
对任意 $n\ge 1$、$m\ge 2$，设 $W_{(m)}\in M_n(\mathcal O_L)$ 满足
$$W_{(m)}\equiv I_n\pmod{2\mathcal O_L},\qquad W_{(m)}^{\mathsf T}W_{(m)}\equiv I_n\pmod{2^m\mathcal O_L},\qquad \operatorname{diag}(W_{(m)}^{\mathsf T}W_{(m)}-I_n)\equiv 0\pmod{2^{m+1}\mathcal O_L}.$$
写 $W_{(m)}=I_n+2X$，$S:=2^{-m}(W_{(m)}^{\mathsf T}W_{(m)}-I_n)\in M_n(\mathcal O_L)$；则 $S$ 对称且 $S_{aa}\in 2\mathcal O_L$（$\forall a$）。取 $Y\in M_n(\mathcal O_L)$ 使 $Y_{aa}:=-S_{aa}/2\in\mathcal O_L$，$Y_{ab}:=0$（$a<b$），$Y_{ba}:=-S_{ab}$（$a<b$），则 $S+Y+Y^{\mathsf T}=0$。令 $W_{(m+1)}:=W_{(m)}+2^mY$，则
$$W_{(m+1)}^{\mathsf T}W_{(m+1)}-I_n = 2^m(S+Y+Y^{\mathsf T}) + 2^{m+1}(X^{\mathsf T}Y+Y^{\mathsf T}X)+2^{2m}Y^{\mathsf T}Y = 2^{m+1}(X^{\mathsf T}Y+Y^{\mathsf T}X)+2^{2m}Y^{\mathsf T}Y.$$
因 $m\ge 2$ 有 $2m\ge m+2$，故 $W_{(m+1)}^{\mathsf T}W_{(m+1)}\equiv I_n\pmod{2^{m+1}\mathcal O_L}$；而且其对角元为
$$2^{m+1}\cdot 2(X^{\mathsf T}Y)_{aa}+2^{2m}(Y^{\mathsf T}Y)_{aa}\equiv 0\pmod{2^{m+2}\mathcal O_L}.$$
由此满足 $m+1$ 层的全部假设。从 $m=M$ 起归纳得到 Cauchy 序列 $(W_{(m)})_{m\ge M}$，在完备环 $M_n(\mathcal O_L)$ 中收敛到 $\widetilde W\in \Gamma_n(L)$ 且 $\widetilde W\equiv W_{(M)}\pmod{2^M\mathcal O_L}$。

*第三步：回到 $U$。*  
由第一步及定理 1.1 取基点 $U_0\in\mathscr S_F(A)$，置 $W:=U_0^{\mathsf T}U=W_{\mathrm{diag}}+2^MW_{\mathrm{off}}$（其中 $W_{\mathrm{diag}}=\operatorname{diag}(W_1,\ldots,W_r)$ 为分块对角部分，$W_{\mathrm{off}}$ 对角块为零）。因 $W^{\mathsf T}W=U^{\mathsf T}U$ 且 $2M\ge M+2>M+1$，同第一步得
$$\operatorname{diag}(W_{\mathrm{diag}}^{\mathsf T}W_{\mathrm{diag}}-I_d)\equiv \operatorname{diag}(W^{\mathsf T}W-I_d)=\operatorname{diag}(U^{\mathsf T}U-I_d)\equiv 0\pmod{2^{M+1}\mathcal O_L}.$$
于是每一块 $W_i$ 满足第二步的条件，可提升为 $\widetilde W_i\in\Gamma_{n_i}(L)$ 使 $\widetilde W_i\equiv W_i\pmod{2^M\mathcal O_L}$。置 $\widetilde U:=U_0\operatorname{diag}(\widetilde W_1,\ldots,\widetilde W_r)\in\mathscr S_L(A)$，则 $\widetilde U\equiv U_0W_{\mathrm{diag}}\equiv U_0W=U\pmod{2^M\mathcal O_L}$，故 $\bar U\in\mathscr R_{L,M}(A)$。$\square$

---

#### 定理 1.3（$\mathscr R_{L,M}(A)$ 与 $\mathscr C_{L,M}(A)$ 的精确基数、空集条件与真包含反例）

对任意合法输入 $A$、$L\in\{F,K_{-1},K_2\}$ 及 $M\ge 2$，记 $e_F=1,e_{K_{-1}}=e_{K_2}=2$，$D=\sum_{i=1}^r\binom{n_i}{2}$，$d=\sum_{i=1}^r n_i$：

1. **$\mathscr R_{L,M}(A)$**：
   - **空集条件**：$\mathscr R_{L,M}(A)=\emptyset \iff \exists i,\;\tau_i(A)=1$（仅当 $r\ge 2$ 时可发生）。
   - **精确基数**：当 $\forall i,\;\tau_i(A)=0$ 时，
     $$\bigl|\mathscr R_{L,M}(A)\bigr|=2^{e_L(M-1)D+r}.$$
2. **$\mathscr C_{L,M}(A)$**：
   - **当 $M=2$ 时**：**永不为空**（即使 $\mathscr S_L(A)=\emptyset$），且恒有
     $$\bigl|\mathscr C_{L,2}(A)\bigr|=2^{e_L(D+d)}.$$
   - **当 $M\ge 3$ 时**：**空集条件**为 $\mathscr C_{L,M}(A)=\emptyset \iff \exists i,\;\tau_i(A)=1$；当 $\forall i,\;\tau_i(A)=0$ 时，
     $$\bigl|\mathscr C_{L,M}(A)\bigr|=2^{e_L\bigl((M-1)D+d\bigr)+r}.$$

**证明**：  
空集条件已由定理 1.1、引理 1.2（$M=2$ 时 $\mathscr C_{L,2}(A)\cong\prod_i \Gamma_{n_i,2}^{\mathscr C}(L)\ni I_d$）及定理 1.1 必要性（$M\ge 3$）完全确定。由引理 1.2 与推论 1.1，只需对单块 $n\ge 1$ 计算 $|\Gamma_{n,M}^{\mathscr C}(L)|$ 与 $|\Gamma_{n,M}^{\mathscr R}(L)|$，再对 $i=1,\ldots,r$ 求积。

**第一步：$M=2$ 的单块计数**。  
任意 $\bar W\in M_n(\mathcal O_L/4\mathcal O_L)$ 满足 $\bar W\equiv I_n\pmod{2\mathcal O_L}$ 可唯一写作 $\bar W=I_n+2X\bmod 4\mathcal O_L$，$X\in M_n(\mathcal O_L/2\mathcal O_L)$。展开得
$$\bar W^{\mathsf T}\bar W=I_n+2(X+X^{\mathsf T})+4X^{\mathsf T}X\equiv I_n+2(X+X^{\mathsf T})\pmod{4\mathcal O_L},$$
故 $\bar W\in\Gamma_{n,2}^{\mathscr C}(L)\iff X^{\mathsf T}=X\in\operatorname{Sym}_n(\mathcal O_L/2\mathcal O_L)$，因此
$$\bigl|\Gamma_{n,2}^{\mathscr C}(L)\bigr|=q_L^{\binom{n+1}{2}}=2^{e_L\binom{n+1}{2}}.$$

再由定理 1.2，$\bar W=I_n+2X\in\Gamma_{n,2}^{\mathscr R}(L)$ 当且仅当对所有 $a=1,\ldots,n$ 有 $(W^{\mathsf T}W-I_n)_{aa}\equiv 0\pmod{8\mathcal O_L}$，即
$$X_{aa}+X_{aa}^2+\sum_{b\ne a} X_{ba}^2 \equiv 0\pmod{2\mathcal O_L}\qquad(\forall a=1,\ldots,n). \tag{$\ast$}$$
注意：对任意 $n\ge 1$，完全图 $K_n$ 的 $\mathbb F_2$-关联映射 $\operatorname{Alt}_n(\mathbb F_2)\to\mathbb F_2^n$，$M\mapsto \bigl(\sum_{b\ne a} M_{ab}\bigr)_{a=1}^n$，其像恰为偶权超平面 $\{y\in\mathbb F_2^n:\sum_a y_a=0\}$（$n=1$ 时显然为 $\{0\}$；$n\ge 2$ 时，任意 $a\le n-1$ 取边 $(a,n)$ 可自由翻转第 $a$ 与第 $n$ 分量，故像维数为 $n-1$），因此该线性方程组 $\sum_{b\ne a}M_{ab}=0$（$\forall a$）在 $\operatorname{Alt}_n(\mathbb F_2)$ 中的解空间维数为 $\binom{n}{2}-(n-1)=\binom{n-1}{2}$。

现在分三种域求解 $(\ast)$：
- **$L=F$**：$\mathcal O_F/2\mathcal O_F=\mathbb F_2$ 中 $x+x^2=0$ 且 $x^2=x$，故 $(\ast)$ 化为 $\sum_{b\ne a}X_{ab}=0$（$\forall a$）。对角元 $X_{aa}\in\mathbb F_2$ 完全自由（$2^n$ 种），非对角部分属于 $\operatorname{Alt}_n(\mathbb F_2)$ 中上述解空间（$2^{\binom{n-1}{2}}$ 种），故
  $$\bigl|\Gamma_{n,2}^{\mathscr R}(F)\bigr|=2^n\cdot 2^{\binom{n-1}{2}}=2^{\binom{n}{2}+1}.$$
- **$L=K_{-1}$**：写 $X=U+V\theta_{-1}$（$U,V\in\operatorname{Sym}_n(\mathbb F_2)$）。在 $\mathcal O_{-1}/2\mathcal O_{-1}$ 中，$(u+v\theta_{-1})^2\equiv u+v$，$(u+v\theta_{-1})+(u+v\theta_{-1})^2\equiv v+v\theta_{-1}$。分离 $(\ast)$ 的 $\theta_{-1}$-部与 $1$-部得
  $$V_{aa}=0\ (\forall a),\qquad \sum_{b\ne a}(U_{ab}+V_{ab})=0\ (\forall a).$$
  于是 $U_{aa}\in\mathbb F_2$（$2^n$ 种）与 $V\in\operatorname{Alt}_n(\mathbb F_2)$（$2^{\binom{n}{2}}$ 种）自由，而 $U+V$ 的非对角部分有 $2^{\binom{n-1}{2}}$ 种选法，故
  $$\bigl|\Gamma_{n,2}^{\mathscr R}(K_{-1})\bigr|=2^n\cdot 2^{\binom{n}{2}}\cdot 2^{\binom{n-1}{2}}=2^{n^2-n+1}=2^{2\binom{n}{2}+1}.$$
- **$L=K_2$**：写 $X=U+V\theta_2$（$U,V\in\operatorname{Sym}_n(\mathbb F_2)$）。在 $\mathcal O_2/2\mathcal O_2$ 中，$(u+v\theta_2)^2\equiv u$，$(u+v\theta_2)+(u+v\theta_2)^2\equiv v\theta_2$。分离 $(\ast)$ 的 $\theta_2$-部与 $1$-部得
  $$V_{aa}=0\ (\forall a),\qquad \sum_{b\ne a}U_{ab}=0\ (\forall a).$$
  同样有 $U_{aa}$（$2^n$ 种）、$V\in\operatorname{Alt}_n(\mathbb F_2)$（$2^{\binom{n}{2}}$ 种）与 $U$ 的非对角部分（$2^{\binom{n-1}{2}}$ 种），故
  $$\bigl|\Gamma_{n,2}^{\mathscr R}(K_2)\bigr|=2^{2\binom{n}{2}+1}.$$

统一写作 $|\Gamma_{n,2}^{\mathscr R}(L)|=2^{e_L\binom{n}{2}+1}$。

**第二步：从精度 $M$ 到 $M+1$（$M\ge 2$）的提升纤维计数**。  
考虑自然约化映射 $\pi_M^{\mathscr C}:\Gamma_{n,M+1}^{\mathscr C}(L)\to \Gamma_{n,M}^{\mathscr C}(L)$。
- 若 $\bar W\in\Gamma_{n,M}^{\mathscr C}(L)\setminus \Gamma_{n,M}^{\mathscr R}(L)$，由定理 1.2 的良定性，对 $\bar W$ 的任意提升 $W'\in M_n(\mathcal O_L)$ 均有 $\operatorname{diag}((W')^{\mathsf T}W'-I_n)\not\equiv 0\pmod{2^{M+1}\mathcal O_L}$，故 $W'$ 不可能满足 $(W')^{\mathsf T}W'\equiv I_n\pmod{2^{M+1}\mathcal O_L}$，即纤维为空。
- 若 $\bar W\in\Gamma_{n,M}^{\mathscr R}(L)$，固定一个真正解提升 $W_0\in\Gamma_n(L)$（$W_0^{\mathsf T}W_0=I_n$）。$\bar W$ 在 $M_n(\mathcal O_L/2^{M+1}\mathcal O_L)$ 中的任意提升唯一写作 $\bar W'=W_0+2^MY\bmod 2^{M+1}\mathcal O_L$（$Y\in M_n(\mathcal O_L/2\mathcal O_L)$）。因 $W_0\equiv I_n\pmod{2\mathcal O_L}$ 且 $M\ge 2$（故 $2M\ge M+2$）：
  $$(W_0+2^MY)^{\mathsf T}(W_0+2^MY)-I_n = 2^M(W_0^{\mathsf T}Y+Y^{\mathsf T}W_0)+2^{2M}Y^{\mathsf T}Y\equiv 2^M(Y+Y^{\mathsf T})\pmod{2^{M+1}\mathcal O_L}.$$
  故 $\bar W'\in\Gamma_{n,M+1}^{\mathscr C}(L)\iff Y\in\operatorname{Sym}_n(\mathcal O_L/2\mathcal O_L)$，纤维大小为 $q_L^{\binom{n+1}{2}}=2^{e_L\binom{n+1}{2}}$。
- 进一步，对上述 $\bar W'=W_0+2^MY\in\Gamma_{n,M+1}^{\mathscr C}(L)$，考察其对角元模 $2^{M+2}\mathcal O_L$：因 $2M\ge M+2$ 且 $W_0\equiv I_n\pmod{2\mathcal O_L}$，
  $$\bigl((W_0+2^MY)^{\mathsf T}(W_0+2^MY)-I_n\bigr)_{aa}=2^{M+1}(W_0^{\mathsf T}Y)_{aa}+2^{2M}(Y^{\mathsf T}Y)_{aa}\equiv 2^{M+1}Y_{aa}\pmod{2^{M+2}\mathcal O_L}.$$
  由定理 1.2，$\bar W'\in\Gamma_{n,M+1}^{\mathscr R}(L)\iff Y_{aa}\equiv 0\pmod{2\mathcal O_L}$（$\forall a$），即 $Y\in\operatorname{Alt}_n(\mathcal O_L/2\mathcal O_L)$，纤维大小为 $q_L^{\binom{n}{2}}=2^{e_L\binom{n}{2}}$。

由归纳法立即得对所有 $M\ge 2$：
$$\bigl|\Gamma_{n,M}^{\mathscr R}(L)\bigr|=2^{e_L\binom{n}{2}+1}\cdot \bigl(2^{e_L\binom{n}{2}}\bigr)^{M-2}=2^{e_L(M-1)\binom{n}{2}+1},$$
而对所有 $M\ge 3$：
$$\bigl|\Gamma_{n,M}^{\mathscr C}(L)\bigr|=\bigl|\Gamma_{n,M-1}^{\mathscr R}(L)\bigr|\cdot 2^{e_L\binom{n+1}{2}}=2^{e_L\bigl((M-1)\binom{n}{2}+n\bigr)+1}.$$
将各块 $n_1,\ldots,n_r$ 相乘，并利用 $\sum_i \binom{n_i}{2}=D$、$\sum_i n_i=d$、$\sum_i 1=r$，即得定理全部基数公式。

**$\mathscr R_{L,M}(A)\subsetneq \mathscr C_{L,M}(A)$ 的全部真包含情形及显式例子**：  
比较基数可知，$\mathscr R_{L,M}(A)=\mathscr C_{L,M}(A)$ 仅发生于两类平凡情形：(a) $M\ge 3$ 且 $\exists i,\;\tau_i(A)=1$（二者皆为空）；(b) $M=2$、$L=F$、$\forall i,\;\tau_i(A)=0$ 且 $n_1=\cdots=n_r=1$（二者皆有基数 $2^r$）。在其余一切情形下皆有严格真包含，以下取 $A_i=E_i$（$\forall i$）（可行情形；不可行且 $M=2$ 的例子见定理 1.1）：
- 对任意 $M\ge 3$、任意 $L\in\{F,K_{-1},K_2\}$ 及任意块秩：取 $\bar U:=I_d+2^{M-1}e_1e_1^{\mathsf T}\bmod 2^M\mathcal O_L$。由 $2M-2\ge M+1$ 得 $(U^{\mathsf T}U-I_d)_{11}=2^M+2^{2M-2}\equiv 2^M\pmod{2^{M+1}\mathcal O_L}$，故 $\bar U\in\mathscr C_{L,M}(A)\setminus \mathscr R_{L,M}(A)$。
- 对 $M=2$、$L=K_\mu$ 及任意块秩：取 $\bar U:=I_d+2\theta_\mu e_1e_1^{\mathsf T}\bmod 4\mathcal O_\mu$。则 $(U^{\mathsf T}U-I_d)_{11}=4\mu+4\theta_\mu\equiv 0\pmod{4\mathcal O_\mu}$ 但 $\not\equiv 0\pmod{8\mathcal O_\mu}$，故 $\bar U\in\mathscr C_{K_\mu,2}(A)\setminus \mathscr R_{K_\mu,2}(A)$。
- 对 $M=2$、$L=F$ 且 $\max_i n_i\ge 2$：取某块 $I_k$（$n_k\ge 2$）中两不同下标 $p,q\in I_k$，取 $\bar U:=I_d+2(e_pe_q^{\mathsf T}+e_qe_p^{\mathsf T})\bmod 4$。则 $U^{\mathsf T}U-I_d=4(e_pe_q^{\mathsf T}+e_qe_p^{\mathsf T})+4(e_pe_p^{\mathsf T}+e_qe_q^{\mathsf T})\equiv 0\pmod 4$，但 $(U^{\mathsf T}U-I_d)_{pp}=4\not\equiv 0\pmod 8$，故 $\bar U\in\mathscr C_{F,2}(A)\setminus \mathscr R_{F,2}(A)$。$\square$

---

## 二、第 2 题完整解答

### 2.1 固定点集的具体矩阵类与基域对应集合的精确关系

**定理 2.1（$\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$ 与 $\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$ 的精确刻画）**  
对任意合法输入 $A$、$\mu\in\{-1,2\}$ 及 $M\ge 2$（其中矩阵类均在 $M_d(\mathcal O_\mu/2^M\mathcal O_\mu)$ 中理解，且 $Z\in\operatorname{Sym}_{\mathbf n}(\mathbb F_2)$ 经任意整提升乘以 $2^{M-1}$ 在模 $2^M\mathcal O_\mu$ 下良定）：

1. **$\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$ 的具体矩阵类**：
   $$\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}=\bigl\{\bar U_0 + 2^{M-1}\theta_\mu Z : \bar U_0\in\mathscr C_{F,M}(A),\; Z\in\operatorname{Sym}_{\mathbf n}(\mathbb F_2)\bigr\},$$
   且映射 $(\bar U_0,Z)\mapsto \bar U_0+2^{M-1}\theta_\mu Z$ 是 $\mathscr C_{F,M}(A)\times \operatorname{Sym}_{\mathbf n}(\mathbb F_2)\xrightarrow{\sim}\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$ 的双射（若 $\mathscr C_{F,M}(A)=\emptyset$，两侧皆为空）。等价地，$\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}=\mathscr C_{F,M}(A)\cdot\bigl(I_d+2^{M-1}\theta_\mu\operatorname{Sym}_{\mathbf n}(\mathbb F_2)\bigr)$。

2. **$\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$ 的具体矩阵类**：
   - 当 **$M\ge 3$**，或当 **$M=2$ 且 $\mu=2$** 时：
     $$\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}=\bigl\{\bar U_0 + 2^{M-1}\theta_\mu Z : \bar U_0\in\mathscr R_{F,M}(A),\; Z\in\operatorname{Alt}_{\mathbf n}(\mathbb F_2)\bigr\};$$
   - 当 **$M=2$ 且 $\mu=-1$** 时：
     $$\mathscr R_{K_{-1},2}(A)^{\sigma_{-1}}=\bigl\{\bar U_0 + 2(1+\theta_{-1}) Z : \bar U_0\in\mathscr R_{F,2}(A),\; Z\in\operatorname{Alt}_{\mathbf n}(\mathbb F_2)\bigr\}.$$
   （特别地，当 $M=2$ 时可用素元 $\pi_{-1}=1+\theta_{-1},\pi_2=\theta_2$ 统一写成 $\mathscr R_{K_\mu,2}(A)^{\sigma_\mu}=\{\bar U_0+2\pi_\mu Z:\bar U_0\in\mathscr R_{F,2}(A),\;Z\in\operatorname{Alt}_{\mathbf n}(\mathbb F_2)\}$。）  
   在上述所有情形下，对应 $(\bar U_0,Z)\mapsto \bar U$ 都是 $\mathscr R_{F,M}(A)\times \operatorname{Alt}_{\mathbf n}(\mathbb F_2)\xrightarrow{\sim}\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$ 的双射（不可行时两侧皆空）。

3. **与基域对应集合的精确关系**：
   - 对 $\mathscr C$：恒有 $\mathscr C_{F,M}(A)=\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\cap M_d(\mathbb Z/2^M\mathbb Z)$（即 $\theta_\mu$-分量为零的类）；非空时，$\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$ 是 $\mathscr C_{F,M}(A)$ 在阶为 $2^{D+d}\ge 2$ 的初等 Abel $2$-群 $I_d+2^{M-1}\theta_\mu\operatorname{Sym}_{\mathbf n}(\mathbb F_2)$ 作用下的自由陪集并，故**只要非空即严格真包含** $\mathscr C_{F,M}(A)\subsetneq \mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$。
   - 对 $\mathscr R$：恒有 $\mathscr R_{F,M}(A)=\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\cap M_d(\mathbb Z/2^M\mathbb Z)=\mathscr R_{K_\mu,M}(A)\cap M_d(\mathbb Z/2^M\mathbb Z)$；非空时，$|\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}|=2^D|\mathscr R_{F,M}(A)|$，从而（在 $\mathscr S_F(A)\ne\emptyset$ 前提下）：
     $$\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}=\mathscr R_{F,M}(A)\iff D=0\iff n_1=\cdots=n_r=1.$$
   - **实部投影的精细差异**：当 $M\ge 3$ 或 $\mu=2$ 时，$\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$ 中每个类的 $\mathbb Z/2^M\mathbb Z$-分量（实部）自动属于 $\mathscr R_{F,M}(A)$；而当 $M=2$、$\mu=-1$ 且 $D>0$ 时，$\bar U=\bar U_0+2(1+\theta_{-1})Z$ 的实部为 $\bar U_0+2Z\in\mathscr C_{F,2}(A)$，它**不必**属于 $\mathscr R_{F,2}(A)$。
   - **精度 $M=2$ 的退化现象**：对所有 $U=I_d+2X\in M_d(\mathcal O_\mu)$，因 $\sigma_\mu(X)\equiv X\pmod{2\mathcal O_\mu}$，恒有 $\sigma_\mu(U)\equiv U\pmod{4\mathcal O_\mu}$，故 $\sigma_\mu$ 在 $\mathscr C_{K_\mu,2}(A)$ 与 $\mathscr R_{K_\mu,2}(A)$ 上作用均平凡，即 $\mathscr C_{K_\mu,2}(A)^{\sigma_\mu}=\mathscr C_{K_\mu,2}(A)$ 且 $\mathscr R_{K_\mu,2}(A)^{\sigma_\mu}=\mathscr R_{K_\mu,2}(A)$。

**证明**：  
由第 0.2 节，任意 $\bar U\in M_d(\mathcal O_\mu/2^M\mathcal O_\mu)^{\sigma_\mu}$ 可唯一表示为 $\bar U=\bar U_0+2^{M-1}\theta_\mu Z\bmod 2^M\mathcal O_\mu$，其中 $\bar U_0\in M_d(\mathbb Z/2^M\mathbb Z)$、$Z\in M_d(\mathbb F_2)$。任取整提升 $U_0,Z\in M_d(\mathbb Z_2)$ 并置 $U:=U_0+2^{M-1}\theta_\mu Z$。

(1) 显然 $U\equiv I_d\pmod{2\mathcal O_\mu}\iff U_0\equiv I_d\pmod 2$。计算得
$$U^{\mathsf T}U=\bigl(U_0^{\mathsf T}U_0+2^{2M-2}\mu Z^{\mathsf T}Z\bigr)+2^{M-1}\theta_\mu\bigl(U_0^{\mathsf T}Z+Z^{\mathsf T}U_0\bigr),$$
$$U^{\mathsf T}A_iU=\bigl(U_0^{\mathsf T}A_iU_0+2^{2M-2}\mu Z^{\mathsf T}A_iZ\bigr)+2^{M-1}\theta_\mu\bigl(U_0^{\mathsf T}A_iZ+Z^{\mathsf T}A_iU_0\bigr).$$
因 $M\ge 2$，有 $2M-2\ge M$，故 $2^{2M-2}\mu(\cdots)\equiv 0\pmod{2^M}$。分离 $1$-部与 $\theta_\mu$-部模 $2^M$：
- $1$-部条件恰为 $U_0^{\mathsf T}U_0\equiv I_d\pmod{2^M}$ 且 $[U_0^{\mathsf T}A_iU_0,E_j]\equiv 0\pmod{2^M}$（$\forall i,j$），即 $\bar U_0\in\mathscr C_{F,M}(A)$。
- $\theta_\mu$-部条件为 $U_0^{\mathsf T}Z+Z^{\mathsf T}U_0\equiv 0\pmod 2$ 且 $[U_0^{\mathsf T}A_iZ+Z^{\mathsf T}A_iU_0,E_j]\equiv 0\pmod 2$（$\forall i,j$）。因 $U_0\equiv I_d\pmod 2$ 且 $A_i\equiv E_i\pmod 2$，前者等价于 $Z^{\mathsf T}\equiv Z\pmod 2$；在此下 $U_0^{\mathsf T}A_iZ+Z^{\mathsf T}A_iU_0\equiv E_iZ+ZE_i\pmod 2$。若 $Z$ 分块对角，则 $E_iZ+ZE_i=2E_iZ\equiv 0\pmod 2$ 自动与 $E_j$ 交换；反之，对任意 $k\ne i$，由 $E_i[E_iZ+ZE_i,E_i]E_k=-E_iZE_k\equiv 0\pmod 2$ 得 $E_iZE_k\equiv 0\pmod 2$，即 $Z$ 分块对角。故 $\theta_\mu$-部条件恰等价于 $Z\in\operatorname{Sym}_{\mathbf n}(\mathbb F_2)$。

这证明了 (1)（而 $\bar U_0(I_d+2^{M-1}\theta_\mu Z)\equiv \bar U_0+2^{M-1}\theta_\mu Z\pmod{2^M\mathcal O_\mu}$ 来自 $\bar U_0\equiv I_d\pmod 2$）。

(2) 对 $\bar U=\bar U_0+2^{M-1}\theta_\mu Z\in\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$，由定理 1.2，$\bar U\in\mathscr R_{K_\mu,M}(A)$ 当且仅当对所有 $a=1,\ldots,d$ 有 $(U^{\mathsf T}U-I_d)_{aa}\equiv 0\pmod{2^{M+1}\mathcal O_\mu}$。展开对角元：
$$(U^{\mathsf T}U-I_d)_{aa}=\bigl((U_0^{\mathsf T}U_0-I_d)_{aa}+2^{2M-2}\mu(Z^{\mathsf T}Z)_{aa}\bigr)+2^M(U_0^{\mathsf T}Z)_{aa}\theta_\mu.$$
因 $U_0\equiv I_d\pmod 2$，其 $\theta_\mu$-部模 $2^{M+1}$ 恰为 $2^M Z_{aa}\equiv 0\pmod{2^{M+1}}$，等价于 $Z_{aa}\equiv 0\pmod 2$（$\forall a$），即 $Z\in\operatorname{Alt}_{\mathbf n}(\mathbb F_2)$。

再看其 $1$-部模 $2^{M+1}$：
- 若 $M\ge 3$（此时 $2M-2\ge M+1$），或若 $M=2$ 且 $\mu=2$（此时 $2^{2M-2}\mu=8=2^{M+1}$），则 $2^{2M-2}\mu(Z^{\mathsf T}Z)_{aa}\equiv 0\pmod{2^{M+1}}$，故 $1$-部条件恰为 $(U_0^{\mathsf T}U_0-I_d)_{aa}\equiv 0\pmod{2^{M+1}}$（$\forall a$），由定理 1.2 等价于 $\bar U_0\in\mathscr R_{F,M}(A)$。
- 若 $M=2$ 且 $\mu=-1$，则 $2^{2M-2}\mu=-4\equiv 4\pmod 8$，$1$-部条件为
  $$(U_0^{\mathsf T}U_0-I_d)_{aa}+4(Z^{\mathsf T}Z)_{aa}\equiv 0\pmod 8\qquad(\forall a).$$
  令 $\widetilde U_0:=U_0+2Z$。因 $Z\in\operatorname{Alt}_{\mathbf n}(\mathbb F_2)$，易验 $\widetilde U_0\bmod 4\in\mathscr C_{F,2}(A)$，且因 $U_0\equiv I_d\pmod 2$ 与 $Z_{aa}\equiv 0\pmod 2$ 有 $4(U_0^{\mathsf T}Z)_{aa}\equiv 4Z_{aa}\equiv 0\pmod 8$，故
  $$(\widetilde U_0^{\mathsf T}\widetilde U_0-I_d)_{aa}=(U_0^{\mathsf T}U_0-I_d)_{aa}+4(U_0^{\mathsf T}Z)_{aa}+4(Z^{\mathsf T}Z)_{aa}\equiv (U_0^{\mathsf T}U_0-I_d)_{aa}+4(Z^{\mathsf T}Z)_{aa}\pmod 8.$$
  从而 $1$-部条件等价于 $\widetilde U_0\bmod 4\in\mathscr R_{F,2}(A)$。记 $\bar U_0':=\widetilde U_0\bmod 4\in\mathscr R_{F,2}(A)$，则 $\bar U_0=\bar U_0'+2Z\bmod 4$，于是 $\bar U=\bar U_0'+2(1+\theta_{-1})Z\bmod 4\mathcal O_{-1}$。映射 $(\bar U_0',Z)\mapsto \bar U$ 的逆为先读出 $\theta_{-1}$-系数 $Z$，再令 $\bar U_0'=\bar U_0+2Z\bmod 4$，故为双射。

(3) 由 (1)(2) 立得（$\bar U\in M_d(\mathbb Z/2^M\mathbb Z)\iff Z=0$；且任意 $\bar U\in\mathscr R_{K_\mu,M}(A)\cap M_d(\mathbb Z/2^M\mathbb Z)$ 自动被 $\sigma_\mu$ 固定，故属于 $\mathscr R_{F,M}(A)$）。

**全部否定结论的显式例子**（取 $A_i=E_i$，$\forall i$）：
- $\mathscr C_{F,M}(A)\subsetneq\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$（对一切 $M\ge 2$、$\mu\in\{-1,2\}$ 及任意块秩）：取 $\bar U:=I_d+2^{M-1}\theta_\mu e_1e_1^{\mathsf T}\bmod 2^M\mathcal O_\mu\in\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\setminus\mathscr C_{F,M}(A)$。
- $\mathscr R_{F,M}(A)\subsetneq\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$（当 $\max_i n_i\ge 2$ 时对一切 $M\ge 2$、$\mu\in\{-1,2\}$）：取第 3 题定理 3.3 中构造的真正解 $U_M\in\mathscr S_{K_\mu}(A)$，则 $\bar U_M:=U_M\bmod 2^M\mathcal O_\mu\in\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\setminus\mathscr R_{F,M}(A)$。
- 当 $M=2$、$\mu=-1$、$\max_i n_i\ge 2$ 时实部不属于 $\mathscr R_{F,2}(A)$ 的例子：取上例 $U_2$（在块 $I_k$ 的两个坐标 $p,q$ 上放置 $R(1+\theta_{-1})=\frac15\begin{pmatrix}-3-4\theta_{-1}&-6+2\theta_{-1}\\6-2\theta_{-1}&-3-4\theta_{-1}\end{pmatrix}$），则 $\bar U_2=I_d+2(1+\theta_{-1})(e_pe_q^{\mathsf T}+e_qe_p^{\mathsf T})\bmod 4\mathcal O_{-1}\in\mathscr R_{K_{-1},2}(A)^{\sigma_{-1}}$，其实部为 $I_d+2(e_pe_q^{\mathsf T}+e_qe_p^{\mathsf T})\bmod 4\in\mathscr C_{F,2}(A)\setminus\mathscr R_{F,2}(A)$。$\square$

---

### 2.2 固定点数与 $\langle\sigma_\mu\rangle$-轨道数

**定理 2.2（固定点数与轨道数）**  
因 $\langle\sigma_\mu\rangle\cong\mathbb Z/2\mathbb Z$，对任意 $\sigma_\mu$-不变有限集 $X$，由 Burnside 引理（或轨道长为 $1$ 或 $2$ 的分解），轨道数为 $|X/\langle\sigma_\mu\rangle|=\frac12(|X|+|X^{\sigma_\mu}|)$。结合定理 1.3 与定理 2.1，对任意 $\mu\in\{-1,2\}$ 及 $M\ge 2$：

1. **$\mathscr R_{K_\mu,M}(A)$**：
   - 若 $\exists i,\;\tau_i(A)=1$：固定点数 $=0$，轨道数 $=0$。
   - 若 $\forall i,\;\tau_i(A)=0$：
     $$\bigl|\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\bigr|=2^D\bigl|\mathscr R_{F,M}(A)\bigr|=2^{MD+r},$$
     $$\bigl|\mathscr R_{K_\mu,M}(A)/\langle\sigma_\mu\rangle\bigr|=\frac{2^{2(M-1)D+r}+2^{MD+r}}{2}=2^{MD+r-1}\bigl(2^{(M-2)D}+1\bigr).$$
     （注：当 $M=2$ 或 $D=0$ 时，$\sigma_\mu$ 作用平凡，轨道数等于全集基数 $2^{MD+r}$；当 $M\ge 3$ 且 $D>0$ 时存在长为 $2$ 的非平凡轨道，例如定理 3.3 中构造的 $U_{M-1}\bmod 2^M\mathcal O_\mu$，其 $(q,p)$ 项的 $\theta_\mu$-部 $\equiv 2^{M-2}\pmod{2^{M-1}}$，故 $\sigma_\mu(U_{M-1})\not\equiv U_{M-1}\pmod{2^M\mathcal O_\mu}$。）

2. **$\mathscr C_{K_\mu,M}(A)$**：
   - **当 $M=2$ 时**（对任意合法 $A$ 均非空）：
     $$\bigl|\mathscr C_{K_\mu,2}(A)^{\sigma_\mu}\bigr|=2^{2(D+d)},\qquad \bigl|\mathscr C_{K_\mu,2}(A)/\langle\sigma_\mu\rangle\bigr|=2^{2(D+d)}.$$
   - **当 $M\ge 3$ 且 $\exists i,\;\tau_i(A)=1$ 时**：固定点数 $=0$，轨道数 $=0$。
   - **当 $M\ge 3$ 且 $\forall i,\;\tau_i(A)=0$ 时**：
     $$\bigl|\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\bigr|=2^{D+d}\bigl|\mathscr C_{F,M}(A)\bigr|=2^{MD+2d+r},$$
     $$\bigl|\mathscr C_{K_\mu,M}(A)/\langle\sigma_\mu\rangle\bigr|=\frac{2^{2(M-1)D+2d+r}+2^{MD+2d+r}}{2}=2^{MD+2d+r-1}\bigl(2^{(M-2)D}+1\bigr).$$
     （注：当 $M\ge 3$ 且 $D=0$ 时，$|\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}|=|\mathscr C_{K_\mu,M}(A)|=2^{2d+r}$，$\sigma_\mu$ 仍作用平凡；当 $M\ge 3$ 且 $D>0$ 时，$U_{M-1}\bmod 2^M\mathcal O_\mu$ 同样给出非平凡轨道。）

**证明**：直接将定理 1.3 的基数与定理 2.1 的双射基数代入 $|X/\langle\sigma_\mu\rangle|=\frac12(|X|+|X^{\sigma_\mu}|)$ 即可（因 $r\ge 1$，指数 $MD+r-1\ge 0$ 与 $MD+2d+r-1\ge 0$ 皆非负）。$\square$

---

### 2.3 从精度 $M+1$ 到 $M$ 的约化像与全部非空纤维大小

**定理 2.3（精度 $M+1\to M$ 的约化像与非空纤维大小）**  
设 $M\ge 2$，$L\in\{F,K_{-1},K_2\}$，$\mu\in\{-1,2\}$。

- **情形 A（不可行输入：$\exists i,\;\tau_i(A)=1$）**：  
  因 $M+1\ge 3$，精度 $M+1$ 处的全部集合 $\mathscr R_{L,M+1}(A)$、$\mathscr C_{L,M+1}(A)$、$\mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu}$、$\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}$ 皆为 $\emptyset$。因此全部约化映射的**约化像皆为 $\emptyset$**，**没有非空纤维**（特别地，当 $M=2$ 时，$\mathscr C_{L,2}(A)$ 与 $\mathscr C_{K_\mu,2}(A)^{\sigma_\mu}$ 非空但约化像仍为 $\emptyset=\mathscr R_{L,2}(A)$）。

- **情形 B（可行输入：$\forall i,\;\tau_i(A)=0$）**：  
  六个约化映射（$M+1\to M$）的约化像及任一像点上的非空纤维（皆为常值大小）列表如下：

| 约化映射（$M+1\to M$，$M\ge 2$） | 约化像 | 每个非空纤维的大小 |
|---|---|---|
| $\mathscr R_{F,M+1}(A)\to \mathscr R_{F,M}(A)$ | $\mathscr R_{F,M}(A)$ | $2^D$ |
| $\mathscr R_{K_\mu,M+1}(A)\to \mathscr R_{K_\mu,M}(A)$ | $\mathscr R_{K_\mu,M}(A)$ | $4^D=2^{2D}$ |
| $\mathscr C_{F,M+1}(A)\to \mathscr C_{F,M}(A)$ | $\mathscr R_{F,M}(A)$ | $2^{D+d}$ |
| $\mathscr C_{K_\mu,M+1}(A)\to \mathscr C_{K_\mu,M}(A)$ | $\mathscr R_{K_\mu,M}(A)$ | $4^{D+d}=2^{2(D+d)}$ |
| $\mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu}\to \mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$ | $\mathscr R_{F,M}(A)$ | $4^D=2^{2D}$ |
| $\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}\to \mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$ | $\mathscr R_{F,M}(A)$ | $4^{D+d}=2^{2(D+d)}$ |

**证明**：  
设 $\forall i,\;\tau_i(A)=0$，取基点 $U_*\in\mathscr S_F(A)$，由推论 1.1 将问题约化到各块乘积。

1. **前四个映射**：由定理 1.3 证明第二步，对单块 $n$，$\Gamma_{n,M+1}^{\mathscr C}(L)\to\Gamma_{n,M}^{\mathscr C}(L)$ 的像恰为 $\Gamma_{n,M}^{\mathscr R}(L)$，每个 $\bar W\in\Gamma_{n,M}^{\mathscr R}(L)$（取真正解提升 $W_0\in\Gamma_n(L)$）在 $\Gamma_{n,M+1}^{\mathscr C}(L)$ 中的纤维为 $\{W_0+2^MY\bmod 2^{M+1}\mathcal O_L:Y\in\operatorname{Sym}_n(\mathcal O_L/2\mathcal O_L)\}$，大小为 $q_L^{\binom{n+1}{2}}$；在 $\Gamma_{n,M+1}^{\mathscr R}(L)$ 中的纤维为 $\{W_0+2^MY\bmod 2^{M+1}\mathcal O_L:Y\in\operatorname{Alt}_n(\mathcal O_L/2\mathcal O_L)\}$，大小为 $q_L^{\binom{n}{2}}$。由于 $U_*\equiv I_d\pmod 2$，左乘 $U_*$ 后，任取 $\bar U\in\mathscr R_{L,M}(A)$ 的真正解提升 $U_0\in\mathscr S_L(A)$，纤维分别为 $\{U_0+2^MY:Y\in\operatorname{Sym}_{\mathbf n}(\mathcal O_L/2\mathcal O_L)\}$（大小 $2^{e_L(D+d)}$）与 $\{U_0+2^MY:Y\in\operatorname{Alt}_{\mathbf n}(\mathcal O_L/2\mathcal O_L)\}$（大小 $2^{e_LD}$）。
2. **固定点集上的两个映射**：因 $M+1\ge 3$，由定理 2.1：
   - 任意 $\bar U'\in\mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu}$ 形如 $\bar U'_0+2^M\theta_\mu Z'$，其中 $\bar U'_0\in\mathscr R_{F,M+1}(A)$，$Z'\in\operatorname{Alt}_{\mathbf n}(\mathbb F_2)$。模 $2^M\mathcal O_\mu$ 约化消去 $2^M\theta_\mu Z'$，得 $\bar U'\bmod 2^M\mathcal O_\mu = \bar U'_0\bmod 2^M\in\mathscr R_{F,M}(A)$。反之，对任意 $\bar U_0\in\mathscr R_{F,M}(A)$，取真正解提升 $U_0\in\mathscr S_F(A)$。则 $\bar U_0$ 在 $\mathscr R_{K_\mu,M+1}(A)$ 中的整个纤维 $\{U_0+2^MY:Y\in\operatorname{Alt}_{\mathbf n}(\mathcal O_\mu/2\mathcal O_\mu)\}$ 自动全被 $\sigma_\mu$ 固定（因 $\sigma_\mu(U_0)=U_0$ 且 $2^M\sigma_\mu(Y)\equiv 2^MY\pmod{2^{M+1}\mathcal O_\mu}$）！因此约化像恰为 $\mathscr R_{F,M}(A)$，且任一像点上的非空纤维大小等于全纤维大小 $4^D=2^{2D}$。
   - 同样，任意 $\bar U'\in\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}$ 形如 $\bar U'_0+2^M\theta_\mu Z'$（$\bar U'_0\in\mathscr C_{F,M+1}(A)$，$Z'\in\operatorname{Sym}_{\mathbf n}(\mathbb F_2)$）。模 $2^M\mathcal O_\mu$ 约化得 $\bar U'_0\bmod 2^M\in\operatorname{Im}(\mathscr C_{F,M+1}(A)\to\mathscr C_{F,M}(A))=\mathscr R_{F,M}(A)$。反之，对任意 $\bar U_0\in\mathscr R_{F,M}(A)$（取真正解提升 $U_0\in\mathscr S_F(A)$），它在 $\mathscr C_{K_\mu,M+1}(A)$ 中的整个纤维 $\{U_0+2^MY:Y\in\operatorname{Sym}_{\mathbf n}(\mathcal O_\mu/2\mathcal O_\mu)\}$ 亦自动全被 $\sigma_\mu$ 固定，故约化像恰为 $\mathscr R_{F,M}(A)$，每个非空纤维大小为 $4^{D+d}=2^{2(D+d)}$。$\square$

（注：由表可知，除 $\mathscr R_{L,M+1}(A)\to\mathscr R_{L,M}(A)$ 恒满射、以及前面指出的少数相等情形外，其余约化映射皆非满射，其不在像中的显式反例已分别由定理 1.3 与定理 2.1 的真包含例子给出。）

---

### 2.4 固定矩阵类的真正解提升与逐层相容序列刻画

**定理 2.4（固定矩阵类的提升与逐层相容序列刻画）**  
设 $A$ 为任意合法输入，$\mu\in\{-1,2\}$，$M\ge 2$，设 $\bar U\in\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$（特别可取 $\bar U\in\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$）。则以下五个条件两两等价：
1. $\bar U$ 能提升为 $\sigma_\mu$-固定的真正解 $U\in\mathscr S_{K_\mu}(A)^{\sigma_\mu}=\mathscr S_F(A)$；
2. $\bar U$ 能作为一条逐层相容的 $\sigma_\mu$-固定矩阵类序列 $(\bar U_k)_{k\ge 2}$（或 $(\bar U_k)_{k\ge M}$）在精度 $M$ 的分量，其中 $\bar U_k\in\mathscr C_{K_\mu,k}(A)^{\sigma_\mu}$ 且 $\bar U_{k+1}\equiv \bar U_k\pmod{2^k\mathcal O_\mu}$；
3. $\bar U$ 能作为一条逐层相容的 $\sigma_\mu$-固定矩阵类序列 $(\bar U_k)_{k\ge 2}$（或 $(\bar U_k)_{k\ge M}$）在精度 $M$ 的分量，其中 $\bar U_k\in\mathscr R_{K_\mu,k}(A)^{\sigma_\mu}$ 且 $\bar U_{k+1}\equiv \bar U_k\pmod{2^k\mathcal O_\mu}$；
4. $\bar U$ 在固定点集内至少能提升一步到精度 $M+1$，即 $\bar U\in\operatorname{Im}\bigl(\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}\to\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\bigr)$（亦等价于 $\bar U\in\operatorname{Im}\bigl(\mathscr R_{K_\mu,M+1}(A)^{\sigma_\mu}\to\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\bigr)$）；
5. $\bar U\in\mathscr R_{F,M}(A)$。

按可核验条目条件表述：
- 对 $\bar U\in\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}$：上述条件等价于 **$\bar U\in M_d(\mathbb Z/2^M\mathbb Z)$（即 $\bar U$ 的 $\theta_\mu$-分量为零）且对 $\bar U$ 的任意 $\mathbb Z_2$-提升 $U$ 有 $\operatorname{diag}(U^{\mathsf T}U-I_d)\equiv 0\pmod{2^{M+1}\mathbb Z_2}$**；
- 对 $\bar U\in\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$：上述条件进一步简化为仅需 **$\bar U\in M_d(\mathbb Z/2^M\mathbb Z)$（即 $\bar U$ 的 $\theta_\mu$-分量为零）**。

**证明**：  
- (1) $\iff$ (5)：因 $\mathscr S_{K_\mu}(A)^{\sigma_\mu}=\mathscr S_F(A)$，其模 $2^M\mathcal O_\mu$ 的像按定义即为 $\mathscr R_{F,M}(A)$。
- (1) $\implies$ (3) $\implies$ (2) $\implies$ (4)：若 $U\in\mathscr S_F(A)$ 提升 $\bar U$，置 $\bar U_k:=U\bmod 2^k\mathcal O_\mu$（$k\ge 2$）即得满足 (3)（从而满足 (2)）的逐层相容固定序列；显然 (2) 蕴含在精度 $M+1$ 存在固定提升 $\bar U_{M+1}\in\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}$，即 (4)。
- (4) $\implies$ (5)：直接由定理 2.3，$\operatorname{Im}\bigl(\mathscr C_{K_\mu,M+1}(A)^{\sigma_\mu}\to\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\bigr)=\mathscr R_{F,M}(A)$（无论 $A$ 可行还是不可行）。（注：对 (2) $\implies$ (1) 也可直接由完备性证明：若 $(\bar U_k)_{k\ge M}$ 为逐层相容固定序列，则在 $M_d(\mathcal O_\mu)\cong\varprojlim_k M_d(\mathcal O_\mu/2^k\mathcal O_\mu)$ 中存在唯一极限 $U$，由 $\bigcap_k 2^k\mathcal O_\mu=\{0\}$ 得 $U\in\mathscr S_{K_\mu}(A)$ 且 $\sigma_\mu(U)=U$，即 $U\in\mathscr S_F(A)$。）
- 条目判据直接来自定理 1.2 与定理 2.1(3)。

特别地，任意 $\bar U\in\mathscr C_{K_\mu,M}(A)^{\sigma_\mu}\setminus\mathscr R_{F,M}(A)$（如定理 2.1 所举的 $I_d+2^{M-1}\theta_\mu e_1e_1^{\mathsf T}\bmod 2^M\mathcal O_\mu$）以及当 $\max_i n_i\ge 2$ 时任意 $\bar U\in\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\setminus\mathscr R_{F,M}(A)$（如定理 3.3 中 $U_M\bmod 2^M\mathcal O_\mu$）均既不能提升为 $\sigma_\mu$-固定真正解，也不能作为逐层相容固定序列的分量（甚至连一步固定提升都不存在）。$\square$

---

## 三、第 3 题完整解答

### 3.1 最优逼近精度 $N_{\max}$ 与精确下降块秩

**定理 3.1（最大整数 $N\in\{0,\ldots,M\}$ 与精确下降判别）**  
对固定的块秩 $(n_1,\ldots,n_r)$、$\mu\in\{-1,2\}$ 和 $M\ge 2$，满足题意性质的最大整数 $N\in\{0,\ldots,M\}$ 为
$$N_{\max}(n_1,\ldots,n_r;\mu,M)=\begin{cases} M, & \text{若 } n_1=n_2=\cdots=n_r=1\ (\text{即 } D=0),\\[4pt] M-1, & \text{若 } \max_{1\le i\le r} n_i\ge 2\ (\text{即 } D>0). \end{cases}$$
该界与 $\mu\in\{-1,2\}$ 无关；**精确下降（$N=M$）成立当且仅当全部块秩皆为 $1$**（$n_1=\cdots=n_r=1$）。

**证明（可行性部分：$N=M$ 当 $D=0$，$N=M-1$ 恒成立）**：  
设 $A$ 合法，且 $U\in\mathscr S_{K_\mu}(A)$ 满足 $\sigma_\mu(U)\equiv U\pmod{2^M\mathcal O_\mu}$。由于 $\mathscr S_{K_\mu}(A)\ne\emptyset$，由定理 1.1 知 $\mathscr S_F(A)\ne\emptyset$。

1. **情形 $n_1=\cdots=n_r=1$（$D=0$）**：  
   因 $\mathcal O_\mu$ 是整环，$w^2=1$ 在 $\mathcal O_\mu$ 中仅有解 $w=\pm 1\in 1+2\mathbb Z_2$，故 $\Gamma_1(K_\mu)=\{\pm 1\}=\Gamma_1(F)$。取基点 $U_0\in\mathscr S_F(A)$，由推论 1.1 得
   $$\mathscr S_{K_\mu}(A)=U_0\cdot \prod_{i=1}^r \Gamma_1(K_\mu)=U_0\cdot\{\pm 1\}^r=\mathscr S_F(A).$$
   因此 $U$ 本身已在 $\mathscr S_F(A)$ 中，取 $W:=U\in\mathscr S_F(A)$ 即有 $U=W$，从而 $U\equiv W\pmod{2^M\mathcal O_\mu}$，$N=M$ 成立（精确下降）。

2. **一般块秩下 $N=M-1$ 恒成立**：
   - 若 $M=2$：任取 $W\in\mathscr S_F(A)$，由定义即有 $U\equiv I_d\equiv W\pmod{2\mathcal O_\mu}$，故 $N=1=M-1$ 成立。
   - 若 $M\ge 3$：记 $\bar U:=U\bmod 2^M\mathcal O_\mu\in\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$。由定理 2.1(2)，存在 $\bar U_0\in\mathscr R_{F,M}(A)$ 与 $Z\in\operatorname{Alt}_{\mathbf n}(\mathbb F_2)$ 使
     $$\bar U = \bar U_0 + 2^{M-1}\theta_\mu Z \pmod{2^M\mathcal O_\mu}.$$
     由 $\bar U_0\in\mathscr R_{F,M}(A)$ 取真正解 $W\in\mathscr S_F(A)$ 满足 $W\equiv \bar U_0\pmod{2^M\mathbb Z_2}$。则
     $$U-W\equiv \bar U-\bar U_0 = 2^{M-1}\theta_\mu Z\equiv 0\pmod{2^{M-1}\mathcal O_\mu},$$
     即 $U\equiv W\pmod{2^{M-1}\mathcal O_\mu}$，$N=M-1$ 成立。

最优性（即 $\max_i n_i\ge 2$ 时 $N=M$ 不成立）将在定理 3.3 中由任意精度统一构造证明。$\square$

---

### 3.2 对给定 $(A,U)$ 能取 $N=M$ 的必要充分条件

**定理 3.2（给定 $A,U$ 的精确下降充要条件）**  
设 $A$ 合法，$\mu\in\{-1,2\}$，$M\ge 2$，且 $U\in\mathscr S_{K_\mu}(A)$ 满足 $\sigma_\mu(U)\equiv U\pmod{2^M\mathcal O_\mu}$。将 $U$ 唯一写成 $U=X+Y\theta_\mu$（$X,Y\in M_d(\mathbb Z_2)$），则以下四个条件两两等价：
1. 存在 $W\in\mathscr S_F(A)$ 使 $U\equiv W\pmod{2^M\mathcal O_\mu}$（即对该 $(A,U)$ 可取 $N=M$）；
2. $Y\equiv 0\pmod{2^M M_d(\mathbb Z_2)}$（等价地，$U\bmod 2^M\mathcal O_\mu\in M_d(\mathbb Z/2^M\mathbb Z)$）；
3. $\sigma_\mu(U)\equiv U\pmod{2^{M+1}\mathcal O_\mu}$；
4. $U\bmod 2^M\mathcal O_\mu\in\mathscr R_{F,M}(A)$。

**证明**：  
- (1) $\iff$ (4)：若存在 $W\in\mathscr S_F(A)$ 使 $U\equiv W\pmod{2^M\mathcal O_\mu}$，则 $U\bmod 2^M\mathcal O_\mu = W\bmod 2^M\mathcal O_\mu\in\mathscr R_{F,M}(A)$；反之按 $\mathscr R_{F,M}(A)$ 的定义立即存在这样的 $W$。
- (2) $\iff$ (3)：由 $\sigma_\mu(U)-U=-2Y\theta_\mu$ 立得 $-2Y\theta_\mu\in 2^{M+1}M_d(\mathcal O_\mu)\iff Y\in 2^M M_d(\mathbb Z_2)$。
- (4) $\iff$ (2)：因 $U\in\mathscr S_{K_\mu}(A)$，有 $\bar U:=U\bmod 2^M\mathcal O_\mu\in\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}$。由定理 2.1(3)（或定理 2.4），$\mathscr R_{K_\mu,M}(A)^{\sigma_\mu}\cap M_d(\mathbb Z/2^M\mathbb Z)=\mathscr R_{F,M}(A)$，故 $\bar U\in\mathscr R_{F,M}(A)\iff \bar U\in M_d(\mathbb Z/2^M\mathbb Z)\iff Y\equiv 0\pmod{2^M}$。  
  （亦可直接验证 (2) $\implies$ (1)：写 $U=X+2^M\theta_\mu Y'$，因 $U\in\mathscr S_{K_\mu}(A)$ 与 $2^M\mathcal O_\mu\cap\mathbb Z_2=2^M\mathbb Z_2$ 知 $X\bmod 2^M\in\mathscr C_{F,M}(A)$；再取 $U^{\mathsf T}U=I_d$ 的 $1$-部得 $X^{\mathsf T}X+2^{2M}\mu (Y')^{\mathsf T}Y'=I_d$，由 $2M\ge M+2>M+1$ 得 $\operatorname{diag}(X^{\mathsf T}X-I_d)\equiv 0\pmod{2^{M+1}\mathbb Z_2}$，依定理 1.2 即有 $X\bmod 2^M\in\mathscr R_{F,M}(A)$，从而存在 $W\in\mathscr S_F(A)$ 使 $W\equiv X\equiv U\pmod{2^M\mathcal O_\mu}$。）$\square$

---

### 3.3 最优性证明与任意精度 $M\ge 2$ 的统一显式构造

**定理 3.3（$\max_i n_i\ge 2$ 时 $N=M-1$ 最优的统一构造）**  
设块秩 $(n_1,\ldots,n_r)$ 满足 $\max_{1\le i\le r} n_i\ge 2$，任取 $\mu\in\{-1,2\}$ 与任意整数 $M\ge 2$。固定一个满足 $n_k\ge 2$ 的块 $I_k$ 及其中两个不同坐标 $p,q\in I_k$。取合法输入
$$A_i:=E_i\qquad(i=1,\ldots,r).$$
记素元 $\pi_{-1}:=1+\theta_{-1}$，$\pi_2:=\theta_2$，令
$$t_M:=2^{M-2}\pi_\mu\in\mathcal O_\mu,\qquad c_M:=\frac{1-t_M^2}{1+t_M^2},\qquad s_M:=\frac{2t_M}{1+t_M^2}.$$
定义 $d\times d$ 矩阵 $U_M$ 使其在坐标对 $(p,q)$ 上取 $2\times 2$ 块 $\begin{pmatrix}c_M&-s_M\\s_M&c_M\end{pmatrix}$、在其余坐标上为单位矩阵（其余条目为 $0$）。则对一切 $M\ge 2$ 与 $\mu\in\{-1,2\}$ 统一成立：
1. $U_M\in\mathscr S_{K_\mu}(A)$；
2. $\sigma_\mu(U_M)\equiv U_M\pmod{2^M\mathcal O_\mu}$；
3. 不存在任何 $W\in\mathscr S_F(A)$（事实上不存在任何 $W\in M_d(\mathbb Z_2)$）满足 $U_M\equiv W\pmod{2^M\mathcal O_\mu}$。

从而 $N_{\max}=M-1$ 对所有 $M\ge 2$ 与 $\mu\in\{-1,2\}$ 皆为最优。

**证明**：  
首先验证 $1+t_M^2\in 1+2\mathcal O_\mu\subset\mathcal O_\mu^\times$：
- 当 $\mu=2$ 时，$t_M^2=2^{2M-4}\cdot 2=2^{2M-3}$。因 $M\ge 2$，有 $2M-3\ge 1$，故 $1+t_M^2=1+2^{2M-3}\in 1+2\mathbb Z_2\subset\mathbb Z_2^\times\subset\mathcal O_2^\times$（特别地 $M=2$ 时 $1+t_2^2=3$）。
- 当 $\mu=-1$ 时，$t_M^2=2^{2M-4}(1+\theta_{-1})^2=2^{2M-3}\theta_{-1}$。因 $2M-3\ge 1$，$1+t_M^2\in 1+2\mathcal O_{-1}$，其范数 $(1+2^{2M-3}\theta_{-1})(1-2^{2M-3}\theta_{-1})=1+2^{4M-6}\in 1+4\mathbb Z_2\subset\mathbb Z_2^\times$，故 $1+t_M^2\in\mathcal O_{-1}^\times$（特别地 $M=2$ 时 $1+t_2^2=1+2\theta_{-1}$，$(1+2\theta_{-1})^{-1}=\frac15(1-2\theta_{-1})$）。

因此 $c_M,s_M\in\mathcal O_\mu$，即 $U_M\in M_d(\mathcal O_\mu)$。

**(1) 验证 $U_M\in\mathscr S_{K_\mu}(A)$**：
- 正交性：代数恒等式 $c_M^2+s_M^2=\frac{(1-t_M^2)^2+4t_M^2}{(1+t_M^2)^2}=1$ 给出 $U_M^{\mathsf T}U_M=I_d$，从而 $U_M\in\mathrm{GL}_d(\mathcal O_\mu)$。
- 分块对角化：因 $p,q\in I_k$，矩阵 $U_M$ 与每个 $E_j$ 交换，故 $[U_M^{\mathsf T}A_iU_M,E_j]=[E_i,E_j]=0$（$\forall i,j$）。
- 同余 $U_M\equiv I_d\pmod{2\mathcal O_\mu}$：由 $t_M^2\in 2^{2M-3}\mathcal O_\mu$ 与 $2M-2\ge M\ge 2$，有
  $$c_M-1=\frac{-2t_M^2}{1+t_M^2}\in 2^{2M-2}\mathcal O_\mu\subseteq 2^M\mathcal O_\mu\subseteq 2\mathcal O_\mu,$$
  $$s_M=\frac{2^{M-1}\pi_\mu}{1+t_M^2}\in 2^{M-1}\mathcal O_\mu\subseteq 2\mathcal O_\mu.$$
  故 $U_M\equiv I_d\pmod{2\mathcal O_\mu}$，因此 $U_M\in\mathscr S_{K_\mu}(A)$。

**(2) 验证 $\sigma_\mu(U_M)\equiv U_M\pmod{2^M\mathcal O_\mu}$**：
- 对 $c_M$：上面已证 $c_M\equiv 1\pmod{2^M\mathcal O_\mu}$，于是 $\sigma_\mu(c_M)\equiv 1\equiv c_M\pmod{2^M\mathcal O_\mu}$。
- 对 $s_M$：由 $1+t_M^2\equiv 1\pmod{2\mathcal O_\mu}$ 得 $(1+t_M^2)^{-1}\equiv 1\pmod{2\mathcal O_\mu}$，从而
  $$s_M = 2^{M-1}\pi_\mu(1+t_M^2)^{-1}\equiv 2^{M-1}\pi_\mu\pmod{2^M\mathcal O_\mu}.$$
  由于 $\sigma_\mu(\pi_\mu)-\pi_\mu=-2\theta_\mu$ 对 $\mu=-1,2$ 均成立，故
  $$\sigma_\mu(s_M)-s_M\equiv 2^{M-1}(\sigma_\mu(\pi_\mu)-\pi_\mu)=-2^M\theta_\mu\equiv 0\pmod{2^M\mathcal O_\mu}.$$
  于是 $\sigma_\mu(U_M)\equiv U_M\pmod{2^M\mathcal O_\mu}$。

**(3) 否定 $N=M$**：  
$U_M$ 的 $(q,p)$ 条目为 $s_M\equiv 2^{M-1}\pi_\mu\pmod{2^M\mathcal O_\mu}$，将其按基底 $\{1,\theta_\mu\}$ 展开，其 $\theta_\mu$-系数模 $2^M$ 为 $2^{M-1}\not\equiv 0\pmod{2^M}$。而任意 $W\in M_d(\mathbb Z_2)$ 的 $\theta_\mu$-系数为 $0$，因 $2^M\mathcal O_\mu=2^M\mathbb Z_2\oplus 2^M\mathbb Z_2\theta_\mu$，故不可能有 $U_M\equiv W\pmod{2^M\mathcal O_\mu}$。

（注：作为最低精度 $M=2$ 的显式数值示例，$(p,q)$ 块分别为 $R(\theta_2)=\frac13\begin{pmatrix}-1&-2\theta_2\\2\theta_2&-1\end{pmatrix}$（$\mu=2$）与 $R(1+\theta_{-1})=\frac15\begin{pmatrix}-3-4\theta_{-1}&-6+2\theta_{-1}\\6-2\theta_{-1}&-3-4\theta_{-1}\end{pmatrix}$（$\mu=-1$）。）$\square$