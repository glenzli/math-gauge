存在唯一的这样的映射 \(e_T\)。关键是每条有限轨道最终进入一个周期，而进入周期所需的时间和周期长度可以随元素变化。

首先，\(N_T\) 和 \(P_T\) 都是 \(R\)-子模。对于 \(N_T\)，若 \(T^m x=T^n y=0\)，则 \(T^{\max(m,n)}\) 同时消去 \(x,y\)。对于 \(P_T\)，若 \(T^p x=x\)、\(T^q y=y\)，则 \(T^{pq}\) 同时固定 \(x,y\)。这两个集合也都对 \(R\) 的标量乘法封闭。

此外，
\[
N_T\cap P_T=\{0\}.
\]
事实上，若 \(z\) 同时满足 \(T^n z=0\) 和 \(T^p z=z\)，取足够大的整数 \(k\) 使 \(kp\ge n\)，便有
\[
z=T^{kp}z=0.
\]

对任意 \(x\in M\)，由轨道有限，存在 \(k\ge0\) 和 \(d\ge1\) 使
\[
T^{k+d}x=T^k x.
\]
于是对所有 \(t\ge k\)，都有 \(T^{t+d}x=T^t x\)。取 \(d\) 的一个倍数 \(q\ge k\)，例如 \(q=d(k+1)\)，则
\[
T^d(T^q x)=T^q x,\qquad
T^k(x-T^q x)=T^k x-T^{k+q}x=0.
\]
因此
\[
T^q x\in P_T,\qquad x-T^q x\in N_T.
\]

这给出了每个 \(x\) 的分解，而且分解唯一：若
\[
x=n+p=n'+p',
\qquad n,n'\in N_T,\quad p,p'\in P_T,
\]
则 \(n-n'=p'-p\in N_T\cap P_T\)，故 \(n=n'\)、\(p=p'\)。所以可以定义
\[
e_T(x)=\text{\(x\) 在上述分解中的 \(P_T\) 分量}.
\]
特别地，上面构造的 \(T^q x\) 就是 \(e_T(x)\)；唯一性保证它不依赖于所选的 \(k,d,q\)。

由于 \(N_T,P_T\) 是子模，分解的唯一性还表明 \(e_T\) 是 \(R\)-线性的。于是
\[
M=N_T\oplus P_T,\qquad M\cong N_T\oplus P_T,
\]
其中同构由 \((n,p)\mapsto n+p\) 给出。\(e_T\) 是沿 \(N_T\) 到 \(P_T\) 的投影，因而
\[
\ker e_T=N_T,\qquad \operatorname{im}e_T=P_T,\qquad e_T^2=e_T.
\]

\(T\) 保持 \(P_T\)，且限制 \(T|_{P_T}\) 是自同构。若 \(x\in P_T\) 且 \(T^p x=x\)，则 \(T^{p-1}x\in P_T\)，并且
\[
T(T^{p-1}x)=x,
\]
所以限制是满射；若又有 \(Tx=0\)，则 \(x=T^p x=0\)，所以它也是单射。其逆因此也是 \(R\)-线性的。

最后，该构造与交织映射相容。若 \(aT=T'a\)，则对所有 \(n\ge0\) 有 \(aT^n=(T')^n a\)，从而
\[
a(N_T)\subseteq N_{T'},\qquad a(P_T)\subseteq P_{T'}.
\]
对任意 \(x\in M\)，等式
\[
ax=a(x-e_Tx)+ae_Tx
\]
给出了 \(ax\) 的一个 \(N_{T'}\oplus P_{T'}\) 分解。由分解的唯一性，其周期分量必为 \(e_{T'}(ax)\)，因此
\[
\boxed{\,ae_T=e_{T'}a\,}.
\]