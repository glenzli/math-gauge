## 结论

记 $\beta(f)=\limsup_{n\to\infty} f(n)/n\in[1,+\infty]$，$f^{(k)}$ 为 $f$ 的 $k$ 次复合。

**第 1 问.** $T_f$ 良定，当且仅当 $\beta(f)<\infty$，等价于 $\sup_n f(n)/n<\infty$。对这样的 $f$：
- $T_f$ 处处连续；
- $T_f$ 总是满射；
- $T_f$ 是单射当且仅当 $\lim_n f(n)/n=1$，此时 $T_f$ 是 $X$ 到自身的等距双射；
- 最小 Lipschitz 常数等于 $\beta(f)=\limsup_n f(n)/n$。它总是有限的，所以 $+\infty$ 的情形不会出现。

**第 2 问.** $L_k=\limsup_n f^{(k)}(n)/n$，极限 $R_f=\lim_k L_k^{1/k}=\inf_k L_k^{1/k}$ 存在。全部可能的有序对为
$$\{(L_1,R_f)\}=\{(a,r)\in\mathbb R^2:\ 1\le r\le a\}.$$
构造：对 $1\le r\le a$，当 $k!\le j<(k+1)!$ 时令 $\phi(j)=k!$，再令 $f(j)=\lceil rj\rceil+\lceil (a-r)\phi(j)\rceil$，则 $(L_1,R_f)=(a,r)$。

---

## 0. 记号与基本事实

$[1,M]$ 表示 $\{1,\dots,M\}$。对 $x\in E$，记
$$u_M(x)=\frac1M\sum_{i\le M}|x_i|,\qquad \|x\|=\limsup_M u_M(x),\qquad \|x\|_\infty=\sup_i|x_i|.$$

- $d(x,y)=\|x-y\|$。由 $\limsup$ 的次可加性，$\|\cdot\|$ 是半范数，且 $\|x\|\le\|x\|_\infty$。
- $Z=\{z:\|z\|=0\}$ 是线性子空间，$X=E/Z$，并且 $\bar d([x],[y])=\|x-y\|$。
- 对 $B\subseteq\mathbb N$，记上密度 $\bar\delta(B)=\|\mathbf 1_B\|$。

**(F1)** $f(1)\ge1$ 且 $f(n+1)\ge f(n)+1$，所以 $f(n)\ge n$，从而 $f(n)\to\infty$。

**(F2)** $P_f$ 是线性的，$P_f\mathbf 1=\mathbf 1$，$P_f\mathbf 1_B=\mathbf 1_{f^{-1}(B)}$。由于 $f$ 是单射，$f^{-1}(f(J))=J$。

**(F3)** 若正整数列 $M_t\to\infty$，则 $\limsup_t u_{M_t}(x)\le\|x\|$。

**(F4)** 由线性，$T_f$ 良定当且仅当对一切 $z\in E$，$\|z\|=0\Rightarrow\|P_fz\|=0$。良定时 $\bar d(T_f[x],T_f[y])=\|P_f(x-y)\|$，所以 $L$ 是 Lipschitz 常数当且仅当对一切 $z\in E$ 有 $\|P_fz\|\le L\|z\|$。

## 1. 引理

**引理 1（上界）.** 若 $\beta=\beta(f)<\infty$，则对一切 $x\in E$，$\|P_fx\|\le\beta\|x\|$。

*证.* $f(1),\dots,f(N)$ 是 $[1,f(N)]$ 中 $N$ 个互不相同的数，故
$$u_N(P_fx)\le\frac1N\sum_{i\le f(N)}|x_i|=\frac{f(N)}N\,u_{f(N)}(x).$$
右边两个因子都非负且有界（$f(N)/N\le\sup_n f(n)/n<\infty$，$u_M(x)\le\|x\|_\infty$）。于是由 (F1)(F3)，
$$\|P_fx\|\le\limsup_N\frac{f(N)}N\cdot\limsup_N u_{f(N)}(x)\le\beta\|x\|.\qquad∎$$

**引理 2（检验集）.** 设 $0<s\le1$，正整数列 $(N_k)$ 满足
$$N_k\ge k\sum_{i<k}(N_i+1)\quad\text{对一切 }k\ge1.\tag{G}$$
令 $J_k=\{j\in\mathbb N:\ N_k\le j\le(1+s)N_k\}$，$B=\bigcup_k f(J_k)$。则

(i) $\bar\delta(f^{-1}(B))\ge \dfrac{s}{1+s}$；

(ii) $\bar\delta(B)\le s\cdot\limsup_k \dfrac{N_k}{f(N_k)}$。

*证.* 由 (G)，当 $k\ge2$ 时 $N_k\ge 2N_{k-1}+2>(1+s)N_{k-1}$。所以诸 $J_k$ 两两不交且依次排列。又 $|J_k|=\lfloor sN_k\rfloor+1\in(sN_k,\,sN_k+1]$。

(i) $f$ 是单射，故 $f^{-1}(B)=\bigcup_i J_i\supseteq J_k$。令 $M_k=\lfloor(1+s)N_k\rfloor$，则 $J_k\subseteq[1,M_k]$，且
$$\frac{|f^{-1}(B)\cap[1,M_k]|}{M_k}\ge\frac{|J_k|}{M_k}>\frac{s}{1+s}.$$
由于 $M_k\to\infty$，得 (i)。

(ii) 对 $M\ge f(N_1)$，令 $k=k(M)=\max\{i:\ f(N_i)\le M\}$，它是有限的。当 $i>k$ 时，$f(J_i)\subseteq[f(N_i),\infty)$ 而 $f(N_i)>M$。所以 $B\cap[1,M]\subseteq\bigcup_{i\le k}f(J_i)$。由 $|J_i|\le N_i+1$ 及 (G)，
$$\frac{|B\cap[1,M]|}{M}\le\frac{sN_k+1+N_k/k}{f(N_k)}=\Big(s+\frac1{N_k}+\frac1k\Big)\frac{N_k}{f(N_k)}=:g_k .$$
当 $M\to\infty$ 时 $k(M)\to\infty$，故 $\bar\delta(B)\le\limsup_k g_k$。又 $N_k/f(N_k)\le1$，所以 $\limsup_k g_k\le s\limsup_k N_k/f(N_k)$。∎

**引理 3.** 存在满足 (G) 的数列 $(N_k)$，使得在 $[1,\infty]$ 中 $f(N_k)/N_k\to\beta(f)$。

*证.* 由上极限的定义，存在 $n_t\uparrow\infty$ 使 $f(n_t)/n_t\to\beta(f)$。从中归纳地选取子列 $N_k=n_{t_k}$，满足 $n_{t_k}\ge k\sum_{i<k}(N_i+1)$。子列仍收敛到 $\beta(f)$。∎

## 2. 第 1 问

**良定性.**
- 若 $\beta(f)<\infty$：由引理 1，$\|z\|=0$ 推出 $\|P_fz\|\le\beta\|z\|=0$，再由 (F4) 得 $T_f$ 良定。
- 若 $\beta(f)=\infty$：取引理 3 的数列 $(N_k)$，在引理 2 中取 $s=1$。得到 $\bar\delta(B)=0$，但 $\|P_f\mathbf 1_B\|=\bar\delta(f^{-1}(B))\ge\tfrac12$。即 $\mathbf 1_B\sim0$，而 $P_f\mathbf 1_B\not\sim 0=P_f0$，所以 $T_f$ 不良定。

**最小 Lipschitz 常数等于 $\beta=\beta(f)<\infty$.**
- 由引理 1 与 (F4)，$\beta$ 是一个 Lipschitz 常数。
- 反之，设 $L$ 是任一 Lipschitz 常数。取引理 3 的 $(N_k)$（使 $f(N_k)/N_k\to\beta$），对 $s\in(0,1]$ 用引理 2：
$$\frac{s}{1+s}\le\bar\delta(f^{-1}(B))=\|P_f\mathbf 1_B\|\le L\|\mathbf 1_B\|\le\frac{Ls}{\beta}.$$
所以 $L\ge\beta/(1+s)$。令 $s\to0^+$，得 $L\ge\beta$。

**连续性.** $T_f$ 是 Lipschitz 映射，因此连续。

**满射性.** 对任意 $y\in E$，令 $x_{f(j)}=y_j$，其余分量为 $0$。则 $x\in E$ 且 $P_fx=y$，所以 $T_f$ 是满射。

**单射性.** 令 $A=f(\mathbb N)$。对 $M\ge f(1)$，令 $n=n(M)=|A\cap[1,M]|$。则 $f(n)\le M<f(n+1)$，且 $M\to\infty$ 时 $n(M)\to\infty$。

- 若 $\beta>1$：令 $x=\mathbf 1_{\mathbb N\setminus A}$，则 $P_fx=0$。由于 $|[1,f(N)]\setminus A|=f(N)-N$，
$$\|x\|\ge\limsup_N\Big(1-\frac N{f(N)}\Big)=1-\frac1\beta>0.$$
所以 $[x]\ne[0]$，但 $T_f[x]=T_f[0]$，$T_f$ 不是单射。
- 若 $\beta=1$（因 $f(n)/n\ge1$，这等价于 $f(n)/n\to1$）：
$$\sum_{i\le M}|x_i|\le n\,u_n(P_fx)+(M-n)\|x\|_\infty .$$
因此 $u_M(x)\le u_{n(M)}(P_fx)+\bigl(1-\tfrac{n(M)}M\bigr)\|x\|_\infty$。又
$$1\ge\frac{n(M)}M>\frac{n}{n+1}\cdot\frac{n+1}{f(n+1)}\to1 .$$
由 (F3) 得 $\|x\|\le\|P_fx\|$；结合引理 1 得 $\|P_fx\|=\|x\|$。所以 $T_f$ 是等距映射，从而是单射；再结合满射，它是等距双射。

## 3. 第 2 问

**$L_k$ 的公式.** 设 $c=\sup_n f(n)/n<\infty$。则
$$f^{(k)}(n)=f\bigl(f^{(k-1)}(n)\bigr)\le c\,f^{(k-1)}(n)\le\dots\le c^kn,$$
所以 $f^{(k)}$ 也是允许的。归纳可得 $(P_f^kx)_j=(P_f^{k-1}x)_{f(j)}=x_{f^{(k)}(j)}$，即 $T_f^k=T_{f^{(k)}}$。由第 1 问，
$$L_k=\limsup_n\frac{f^{(k)}(n)}{n}\in[1,\infty).$$

**极限存在.** 首先 $L_k\ge1$，因为 $\|P_{f^{(k)}}\mathbf 1\|=\|\mathbf 1\|=1$。其次，由于
$$\bar d(T^{j+k}u,T^{j+k}v)\le L_j\,\bar d(T^ku,T^kv)\le L_jL_k\,\bar d(u,v),$$
有 $L_{j+k}\le L_jL_k$。

令 $a_k=\log L_k\ge0$，它是次可加的。令 $\lambda=\inf_k a_k/k$。固定 $q$，把 $k$ 写成 $k=pq+t$，其中 $p\ge0$，$1\le t\le q$。则 $a_k\le pa_q+a_t$，于是
$$\frac{a_k}k\le\frac{a_q}q+\frac{\max_{t\le q}a_t}{k}.$$
令 $k\to\infty$ 得 $\limsup_k a_k/k\le a_q/q$；再对 $q$ 取下确界，得 $\limsup_k a_k/k\le\lambda\le\liminf_k a_k/k$。所以极限存在，且
$$R_f=\lim_k L_k^{1/k}=\inf_k L_k^{1/k}.$$
由此 $1\le R_f\le L_1<\infty$。这就是必要条件。

**构造（充分性）.** 固定 $1\le r\le a$。令 $N_k=k!$，当 $N_k\le j<N_{k+1}$ 时令 $\phi(j)=N_k$。$\phi$ 单调不减，$\phi(j)\le j$，$\phi(N_k)=N_k$。令
$$f(j)=\lceil rj\rceil+\lceil(a-r)\phi(j)\rceil .$$

- **$f$ 严格递增：** 由 $r\ge1$ 得 $\lceil r(j+1)\rceil\ge\lceil rj\rceil+1$，而第二项单调不减。
- **基本估计：** 
$$rj+(a-r)\phi(j)\le f(j)<rj+(a-r)\phi(j)+2 .$$
故 $rj\le f(j)<aj+2\le(a+2)j$，且 $f(N_k)\ge aN_k$。
- **$L_1=a$：** 由 $f(j)/j<a+2/j$ 得 $\beta(f)\le a$；由 $f(N_k)/N_k\ge a$ 得 $\beta(f)\ge a$。
- **$R_f\ge r$：** 由 $f(y)\ge ry$ 得 $f^{(m)}(n)\ge r^mn$，从而 $L_m\ge r^m$，$R_f\ge r$。
- **$R_f\le r$：** 取 $\rho>r$（于是 $\rho>1$）。令 $C=\dfrac{a-r}{\rho-1}\ge0$，$V(y)=y+C\phi(y)$，则 $y\le V(y)\le(1+C)y$，且 $(a-r)+C=\rho C$。当 $y\ge \dfrac{2}{\rho-r}$ 时，
$$f(y)+C\phi(y)<ry+2+\rho C\phi(y)\le\rho V(y).\tag{$*$}$$
  - 若 $\phi(f(y))=\phi(y)$，则由 $(*)$ 得 $V(f(y))\le\rho V(y)$。
  - 若 $\phi(f(y))\ne\phi(y)$，则 $V(f(y))\le(1+C)f(y)\le(1+C)\rho V(y)$。

  固定 $m$，取整数 $K\ge(a+2)^m$。设 $n\ge\max\{N_K,\,2/(\rho-r)\}$，且 $n\in[N_k,N_{k+1})$，则 $k\ge K$。令 $x_i=f^{(i)}(n)$。数列 $x_i$ 单调不减，且
$$x_m\le(a+2)^mn<K\,N_{k+1}<(k+2)N_{k+1}=N_{k+2}.$$
所以 $\phi(x_i)$ 只取 $N_k$、$N_{k+1}$ 两个值，并且至多改变一次。于是
$$x_m\le V(x_m)\le(1+C)\rho^mV(x_0)\le(1+C)^2\rho^m n .$$
故 $L_m\le(1+C)^2\rho^m$，从而 $R_f\le\rho$。令 $\rho\downarrow r$，得 $R_f\le r$。

因此 $(L_1,R_f)=(a,r)$。特例：$r=a$ 时 $f(j)=\lceil aj\rceil$；$a=r=1$ 时 $f$ 为恒等映射。

**结论.** 全部可能的有序对恰为 $\{(L_1,R_f):\ 1\le R_f\le L_1<\infty\}$，每一对都由上面的 $f$ 实现。