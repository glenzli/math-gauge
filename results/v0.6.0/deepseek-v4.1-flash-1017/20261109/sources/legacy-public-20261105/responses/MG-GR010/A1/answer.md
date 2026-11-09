约定：\(kX\) 均按题中“所有 \(U\)-小紧 Hausdorff 探针”定义；\(C_{\mathrm{co}}\) 表示紧开拓扑；\(C(A,B)\) 在不带下标时只表示连续映射集合。将 \(kX\) 视为与原空间同一底集、拓扑更细的空间。

---

## S1

设 \(X\) 局部紧 Hausdorff，\(Y,Z\) 任意 Hausdorff。

### 1. 求值映射连续

令
\[
e:C_{\mathrm{co}}(X,Y)\times X\to Y,\qquad e(f,x)=f(x).
\]
取 \((f_0,x_0)\) 及 \(Y\) 中开集 \(O\) 使 \(f_0(x_0)\in O\)。因 \(f_0^{-1}(O)\) 是 \(x_0\) 的开邻域，且 \(X\) 局部紧 Hausdorff，故存在开集 \(U\) 与紧集 \(K\) 使
\[
x_0\in U\subseteq K\subseteq f_0^{-1}(O).
\]
于是
\[
(f_0,x_0)\in [K,O]\times U,
\]
且对任意 \((f,x)\in [K,O]\times U\)，有 \(f(x)\in f(K)\subseteq O\)。故 \(e\) 连续。

### 2. 柯里化双射

定义
\[
\Phi:C(Z\times X,Y)\to C\bigl(Z,C_{\mathrm{co}}(X,Y)\bigr),
\qquad \Phi(f)(z)(x)=f(z,x).
\]

- 对固定 \(z\)，切片 \(f(z,-):X\to Y\) 连续，故 \(\Phi(f)(z)\in C(X,Y)\)。
- 证明 \(\Phi(f):Z\to C_{\mathrm{co}}(X,Y)\) 连续。取 \(z_0\in Z\) 与子基元 \([K,O]\)，并设
  \[
  \Phi(f)(z_0)\in [K,O],
  \]
  即 \(f(\{z_0\}\times K)\subseteq O\)。因 \(K\) 紧，管引理给出 \(z_0\) 的开邻域 \(V\)，使
  \[
  V\times K\subseteq f^{-1}(O).
  \]
  于是 \(\Phi(f)(V)\subseteq [K,O]\)，故 \(\Phi(f)\) 连续。

反过来定义
\[
\Psi:C\bigl(Z,C_{\mathrm{co}}(X,Y)\bigr)\to C(Z\times X,Y),
\qquad \Psi(g)(z,x)=g(z)(x).
\]
由 \(g\times \mathrm{id}_X:Z\times X\to C_{\mathrm{co}}(X,Y)\times X\) 连续以及上面已证的求值映射连续，得
\[
\Psi(g)=e\circ(g\times \mathrm{id}_X)
\]
连续。显然 \(\Psi\circ\Phi=\mathrm{id}\)、\(\Phi\circ\Psi=\mathrm{id}\)。故 \(\Phi\) 是双射；实际上上述两方向均连续，所以还是同胚。

### 3. 自然性

- 对连续 \(u:Z'\to Z\)，
  \[
  \Phi\bigl(f\circ(u\times \mathrm{id}_X)\bigr)=\Phi(f)\circ u.
  \]
- 对连续 \(v:Y\to Y'\)，
  \[
  \Phi\bigl(v\circ f\bigr)
  =C(\mathrm{id}_X,v)\circ \Phi(f),
  \]
  其中 \(C(\mathrm{id}_X,v)(h)=v\circ h\)。
- 若 \(X'\) 也局部紧，\(w:X'\to X\) 连续，则
  \[
  \Phi\bigl(f\circ(\mathrm{id}_Z\times w)\bigr)
  =C(w,\mathrm{id}_Y)\circ\Phi(f),
  \]
  其中 \(C(w,\mathrm{id}_Y)(h)=h\circ w\)。

这些等式逐点验证即可；逆映射的自然性由双射性及复合等式得到。

---

## S2

### (a) profinite 探针与全部紧 Hausdorff 探针给出同一 \(k\) 拓扑

显然，紧 Hausdorff 探针检测得到的拓扑比仅用 profinite 探针检测得到的拓扑更细。只需证反方向：若 \(O\subseteq X\) 使每个 profinite 探针的原像开，则对每个紧 Hausdorff 探针 \(f:K\to X\)，\(f^{-1}(O)\) 开。

取 \(K\) 的底层集合 \(D\)，赋离散拓扑。由 Stone–Čech 紧化的普遍性质，恒等映射 \(D\to K\) 延拓为连续满射
\[
q:\beta D\to K.
\]
这里 \(\beta D\) 是紧完全不连通空间；因 \(D\in U\)，可取 \(\beta D\) 为 \(U\)-小，故它是允许的 profinite 探针。又紧 Hausdorff 空间之间的连续满射是商映射。由假设，
\[
(f\circ q)^{-1}(O)=q^{-1}(f^{-1}(O))
\]
在 \(\beta D\) 中开。因 \(q\) 是商映射，\(f^{-1}(O)\) 在 \(K\) 中开。故所有紧 Hausdorff 探针都通过检测。因此两种探针给出的拓扑相同。

### (b) \(\operatorname{Nat}(h_X,h_Y)\cong C(kX,kY)\)

定义
\[
\Phi:\operatorname{Nat}(h_X,h_Y)\to C(kX,kY)
\]
如下：对自然变换 \(\eta:h_X\to h_Y\)，令
\[
F(x)=\eta_{*}(\bar x),
\]
其中 \(*\) 是单点 profinite 空间，\(\bar x:*\to X\) 是取值为 \(x\) 的映射，并把 \(C(*,X)\)、\(C(*,Y)\) 分别与 \(X,Y\) 的底集等同。

对任意 profinite \(S\)、\(g:S\to X\) 及 \(s:*\to S\)，由自然性，
\[
\eta_S(g)(s)
=\eta_*\bigl(g\circ s\bigr)
=F(g(s)).
\]
因此作为函数
\[
\eta_S(g)=F\circ g.
\]
于是对每个 profinite 探针 \(u:K\to X\)，有
\[
\eta_K(u)=F\circ u\in C(K,Y).
\]
由 (a)，这等价于 \(F:kX\to kY\) 连续。故 \(F\in C(kX,kY)\)。

反过来，若 \(F:kX\to kY\) 连续，定义
\[
\eta_S(g)=j_Y\circ F\circ g,
\qquad g:S\to X,
\]
其中 \(j_Y:kY\to Y\) 是连续恒等映射。因为 \(S\) 紧 Hausdorff，\(g:S\to X\) 自动也是 \(S\to kX\) 的连续映射，故 \(F\circ g\) 有意义且连续。易见 \(\eta\) 是自然变换。两个构造互为逆，故得到双射。该双射与 \(X,Y\) 中的连续映射相容，因而是自然的。

### (c) 何时所有自然变换都由原拓扑连续映射诱导

结论：
\[
\boxed{\text{对固定 }X,\ \forall Y,\ C(X,Y)\to \operatorname{Nat}(h_X,h_Y),\ f\mapsto h_f
\text{ 是双射}\iff kX=X.}
\]

证明：

- 若 \(kX=X\)，由 (b)，任意 \(\eta\in\operatorname{Nat}(h_X,h_Y)\) 对应某个 \(F:kX\to kY\)。因 \(kX=X\)，\(F:X\to kY\) 连续；再复合连续映射 \(kY\to Y\)，得 \(F:X\to Y\) 在原拓扑下连续。且 \(\eta=h_F\)。故所有自然变换都由原拓扑连续映射诱导。

- 反之，假设对所有 Hausdorff \(Y\)，所有自然变换都由原拓扑连续映射诱导。取 \(Y=kX\)。由 (b)，恒等映射
  \[
  \mathrm{id}_{kX}:kX\to kX
  \]
  对应一个自然变换 \(\eta:h_X\to h_{kX}\)。按假设，存在原拓扑连续映射 \(f:X\to kX\) 使 \(\eta=h_f\)。在点上比较得 \(f(x)=x\)，即 \(f=\mathrm{id}_X\)。于是
  \[
  \mathrm{id}_X:X\to kX
  \]
  连续。但 \(kX\) 总比 \(X\) 细，故这意味着 \(kX\subseteq X\)。又总有 \(X\subseteq kX\)，所以 \(kX=X\)。

因此充要条件是 \(X\) 紧生成。

---

## S3

下面使用紧生成 Hausdorff 空间范畴 \(\mathbf{CGH}\) 的标准指数律：若 \(A,B\) 是紧生成 Hausdorff 空间，则
\[
[A,B]:=k\bigl(C_{\mathrm{co}}(A,B)\bigr)
\]
是 \(\mathbf{CGH}\) 中的内 hom，并且对任意紧生成 Hausdorff \(C\)，有自然双射
\[
C(C,[A,B])\cong C(C\times_k A,B).
\]
这里 \(kX,kY\) 由构造是紧生成的，\(S\) 与各种 profinite 空间紧 Hausdorff，因而都是 \(\mathbf{CGH}\) 对象，故条件适用。

### 1. 构造 \(M(X,Y)\)

令
\[
\boxed{M(X,Y):=[kX,kY]=k\bigl(C_{\mathrm{co}}(kX,kY)\bigr).}
\]
其底集为
\[
\boxed{C(kX,kY)}
\]
即从 \(kX\) 到 \(kY\) 的连续映射全体。其拓扑是紧开拓扑的 \(k\)-化：子基为
\[
[K,U]=\{m:kX\to kY\mid m(K)\subseteq U\},
\]
其中 \(K\subseteq kX\) 紧，\(U\subseteq kY\) 开；然后取由所有紧 Hausdorff 探针检测得到的 \(k\) 拓扑。

因 \(kY\) Hausdorff，\(C_{\mathrm{co}}(kX,kY)\) Hausdorff；\(k\)-化只加开集，故 \(M(X,Y)\) 仍 Hausdorff。按定义 \(M(X,Y)\) 是紧生成的。

### 2. 表示定理

先注意对任意 profinite \(S\)，有自然同构
\[
h_S\times h_X\cong h_{S\times_k kX}.
\]
事实上对 profinite \(T\)，因 \(T\in\mathbf{CGH}\) 且 \(S\times_k kX\) 是 \(\mathbf{CGH}\) 积，
\[
C(T,S\times_k kX)\cong C(T,S)\times C(T,kX)
=C(T,S)\times C(T,X),
\]
且 \(C(T,kX)=C(T,X)\)（见 S2(b) 的同样理由）。

于是由 S2(b) 和 \(k(S\times_k kX)=S\times_k kX\)，
\[
\begin{aligned}
H_{X,Y}(S)
&=\operatorname{Nat}(h_S\times h_X,h_Y)\\
&\cong \operatorname{Nat}\bigl(h_{S\times_k kX},h_Y\bigr)\\
&\cong C\bigl(k(S\times_k kX),kY\bigr)\\
&=C(S\times_k kX,kY).
\end{aligned}
\]
再由 \(\mathbf{CGH}\) 指数律，
\[
C(S\times_k kX,kY)
\cong C(S,[kX,kY])
=C(S,M(X,Y)).
\]
所有这些同构关于 \(S\) 的自然映射都是自然的。因此
\[
\boxed{C(S,M(X,Y))\cong H_{X,Y}(S)}
\]
在全部 profinite \(S\) 上自然。

### 3. 构造 \(\mathrm{ev}:h_M\times h_X\to h_Y\)

设
\[
e_{X,Y}:M(X,Y)\times_k kX\to kY
\]
为 \(\mathbf{CGH}\) 中的求值映射。对 profinite \(S\)，定义
\[
(\mathrm{ev}_{X,Y})_S:
C(S,M(X,Y))\times C(S,X)\to C(S,Y)
\]
为：把 \(\beta:S\to X\) 看作 \(S\to kX\) 的连续映射，令
\[
(\mathrm{ev}_{X,Y})_S(\alpha,\beta)
=j_Y\circ e_{X,Y}\circ\langle \alpha,\beta\rangle,
\]
其中 \(j_Y:kY\to Y\) 是连续恒等映射。由于 \(S\) 是紧 Hausdorff，\(\langle\alpha,\beta\rangle:S\to M(X,Y)\times_k kX\) 连续；复合后得到 \(S\to kY\to Y\)。自然性由
\[
\langle\alpha\circ r,\beta\circ r\rangle
=\langle\alpha,\beta\rangle\circ r
\]
直接得到。故 \(\mathrm{ev}\) 确是自然变换。

### 4. 普遍性质

对任意 Hausdorff \(Z\)，考虑
\[
\Theta_Z:\operatorname{Nat}(h_Z,h_M)\to
\operatorname{Nat}(h_Z\times h_X,h_Y),
\qquad
\Theta_Z(\alpha)=\mathrm{ev}\circ(\alpha\times I_X).
\]

由 S2(b) 以及上面的乘积表示，
\[
\operatorname{Nat}(h_Z,h_M)
\cong C(kZ,kM)=C(kZ,M),
\]
而
\[
\operatorname{Nat}(h_Z\times h_X,h_Y)
\cong C(kZ\times_k kX,kY).
\]
这里用了
\[
h_Z\times h_X\cong h_{kZ\times_k kX}
\]
以及 S2(b)。由 \(\mathbf{CGH}\) 指数律，
\[
C(kZ,M)
=C(kZ,[kX,kY])
\cong C(kZ\times_k kX,kY).
\]
这个指数双射正是
\[
F\longmapsto \bigl((z,x)\mapsto e_{X,Y}(F(z),x)\bigr),
\]
亦即复合上 \(\mathrm{ev}\) 的映射。因此 \(\Theta_Z\) 是双射：
\[
\boxed{\operatorname{Nat}(h_Z,h_M)\cong
\operatorname{Nat}(h_Z\times h_X,h_Y).}
\]
且该双射关于 \(Z\) 自然。

### 5. 对 \(X,Y\) 中连续映射的自然性

对连续 \(u:X'\to X\)、\(v:Y\to Y'\)，定义
\[
M(u,v):M(X,Y)\to M(X',Y'),
\qquad
M(u,v)(m)=kv\circ m\circ ku.
\]
这是 \(\mathbf{CGH}\) 内 hom 的函子性给出的连续映射。对 profinite \(S\)、\(\alpha:S\to M(X,Y)\)、\(\beta:S\to X'\)，有逐点等式
\[
\mathrm{ev}_{X',Y'}\bigl(M(u,v)\circ\alpha,\beta\bigr)
=
v\circ \mathrm{ev}_{X,Y}\bigl(\alpha,u\circ\beta\bigr).
\]
等价地，
\[
h_v\circ \mathrm{ev}_{X,Y}\circ
(I_{h_M}\times h_u)
=
\mathrm{ev}_{X',Y'}\circ
(h_{M(u,v)}\times I_{h_{X'}}).
\]
这正是 \(\mathrm{ev}\) 关于 \(X,Y\) 的自然性，也说明上述普遍双射关于 \(X,Y\) 自然。

---

## S4

### 1. 第一可数不保证通常求值映射连续

结论：\(\boxed{\text{不一定连续。}}\)

反例：取
\[
X=\mathbb Q\quad(\text{通常拓扑}),\qquad
Y=\{0,1\}\quad(\text{离散拓扑}).
\]
\(X\) 第一可数 Hausdorff，\(Y\) Hausdorff。证明
\[
e:C_{\mathrm{co}}(\mathbb Q,\{0,1\})\times\mathbb Q
\to \{0,1\}
\]
不连续。

取常值函数 \(1\)，任取 \(q\in\mathbb Q\)。考察开集 \(\{1\}\subseteq Y\)。若 \(e\) 在 \((1,q)\) 连续，则应存在基本邻域
\[
W\times U\subseteq e^{-1}(\{1\}),
\]
其中 \(U\) 是 \(q\) 的开邻域，
\[
W=\bigcap_{i=1}^{n}[K_i,\{1\}]
\]
（\(W\) 的一般有限交中还可能出现 \([K_i,Y]\)，它无约束；可能出现 \([K_i,\varnothing]\)，但常值 \(1\) 不属于它）。令
\[
K=\bigcup_{i=1}^{n}K_i.
\]
每个 \(K_i\) 是 \(\mathbb Q\) 的紧子集。\(\mathbb Q\) 的紧子集没有内点：否则它含有某个有理区间，作为 \(\mathbb R\) 的紧子集（紧性不依赖环境）将含有该区间中的无理点，矛盾。有限并也没有内点。因此 \(U\setminus K\neq\varnothing\)。

取 \(x\in U\setminus K\)。因 \(\mathbb Q\) 零维，存在既开又闭的 \(C\) 使
\[
x\in C\subseteq U\setminus K.
\]
定义
\[
g(y)=
\begin{cases}
0,&y\in C,\\
1,&y\notin C.
\end{cases}
\]
因 \(C\) 既开又闭，\(g\) 连续。又 \(g\) 在 \(K\) 上与常值 \(1\) 相同，故 \(g\in W\)；且 \(x\in U\)。于是
\[
(g,x)\in W\times U,
\]
但
\[
e(g,x)=g(x)=0\notin\{1\},
\]
矛盾。故 \(e\) 不连续。

### 2. 第一可数性足以保证 \(kX=X\)

结论：\(\boxed{\text{是。}}\)

设 \(O\subseteq X\) 是 \(k\)-开集。若 \(O\) 不是原拓扑开集，则存在 \(x\in O\)，使得 \(x\) 的每个邻域都不包含于 \(O\)。取 \(x\) 的可数递减邻域基 \(\{U_n\}_{n<\omega}\)，并选
\[
x_n\in U_n\setminus O.
\]
则 \(x_n\to x\)。令
\[
K=\{x\}\cup\{x_n:n<\omega\}.
\]
任取 \(K\) 的开覆盖。其中一个开集包含 \(x\)，因 \(x_n\to x\)，它包含除有限多个之外的全部 \(x_n\)；剩余有限多个点再用有限多个覆盖元素即可。故 \(K\) 紧。作为 Hausdorff 空间的子空间，\(K\) 紧 Hausdorff。包含映射 \(i:K\to X\) 是紧 Hausdorff 探针。

因 \(O\) 是 \(k\)-开集，\(i^{-1}(O)=O\cap K\) 应在 \(K\) 中开。但
\[
O\cap K=\{x\}.
\]
而 \(\{x\}\) 在 \(K\) 中不开：若它在 \(K\) 中开，则有 \(X\) 中开集 \(V\) 使
\[
V\cap K=\{x\}.
\]
因 \(V\) 是 \(x\) 的邻域，存在 \(n\) 使 \(U_n\subseteq V\)，于是 \(x_n\in V\cap K\)，与 \(V\cap K=\{x\}\) 矛盾。

故 \(O\cap K\) 不开，与 \(O\) 的 \(k\)-开性矛盾。因此 \(O\) 本来就在 \(X\) 中开，所以 \(kX=X\)。

注意：这个结论只说第一可数性给出 \(kX=X\)，并不修复求值映射；上面的 \(\mathbb Q\) 例子同时说明，即使 \(kX=X\)，普通乘积上的求值映射仍可能不连续。

---

## S5

结论：\(\boxed{\text{不一定。}}\)

反例使用 Fortissimo 空间。

取不可数集合 \(D\)，固定 \(p\in D\)。令 \(X=D_{\mathrm{disc}}\) 为离散空间；令
\[
Y=D_{\mathrm{Fort}}
\]
为 Fortissimo 空间，其开集规定为：
\[
U\subseteq D\text{ 开 }
\iff
p\notin U
\quad\text{或}\quad
\bigl(p\in U\text{ 且 }D\setminus U\text{ 可数}\bigr).
\]
即不含 \(p\) 的任意子集都开；含 \(p\) 的开集有可数补集。

验证：

1. **\(Y\) Hausdorff。**  
   若 \(x,y\neq p\)，则 \(\{x\},\{y\}\) 是分离开集。若 \(x\neq p\)，则 \(\{x\}\) 与 \(D\setminus\{x\}\) 是分离开集，后者含 \(p\)，且补集 \(\{x\}\) 可数。

2. **\(Y\) 的紧子集都有限。**  
   设 \(A\subseteq Y\) 紧且无限。若 \(A\setminus\{p\}\) 有限，则 \(A\) 有限，矛盾。故可取可数无限子集 \(C\subseteq A\setminus\{p\}\)。令
   \[
   O=D\setminus C.
   \]
   因 \(C\) 可数，\(O\) 是含 \(p\) 的开集。族
   \[
   \{O\}\cup\{\{c\}:c\in C\}
   \]
   覆盖 \(A\)，但任何有限子覆盖至多包含 \(O\) 与有限多个单点集，遗漏 \(C\) 中无限多个点，仍遗漏 \(A\) 中的点。矛盾。故 \(A\) 有限。

3. 因 \(Y\) 的紧子集全为有限，而有限 Hausdorff 子空间离散，所以对任意 \(O\subseteq Y\) 及任意紧 \(K\subseteq Y\)，\(O\cap K\) 在 \(K\) 中开。故每个 \(O\) 都是 \(kY\)-开集，即
   \[
   kY=Y_{\mathrm{disc}}.
   \]
   显然
   \[
   kX=X_{\mathrm{disc}}.
   \]

令
\[
f=\mathrm{id}_D:X\to Y.
\]
由于 \(Y\) 的拓扑比离散拓扑粗，\(f\) 连续。另一方面，对 profinite \(S\)，\(S\to Y\) 连续当且仅当 \(S\to D_{\mathrm{disc}}\) 连续：连续像 \(f(S)\) 是 \(Y\) 的紧子集，故有限；有限 Hausdorff 像离散，故各纤维开。因此
\[
h_X=h_Y=h_{D_{\mathrm{disc}}}
\]
作为 \(\mathbf{Prof}^{op}\to\mathbf{Set}\) 的函子相同，且
\[
h_f=\mathrm{id}_{h_{D_{\mathrm{disc}}}}
\]
是自然同构。也可由 \(kf:kX\to kY\) 是离散空间之间的恒等同胚，再用 S2(b) 得出。

但 \(f\) 不是原拓扑的同胚：单点集 \(\{p\}\) 在离散空间 \(X\) 中开，而在 Fortissimo 空间 \(Y\) 中不开，因为其余集 \(D\setminus\{p\}\) 不可数。故 \(h_f\) 自然同构不能推出 \(f\) 为普通同胚。

---

## S6

### 1. 连续复合

设
\[
M(X,Y)=[kX,kY]=k(C_{\mathrm{co}}(kX,kY)).
\]
定义
\[
c_{X,Y,Z}:M(Y,Z)\times_k M(X,Y)\to M(X,Z),
\qquad
c_{X,Y,Z}(g,f)=g\circ f.
\]
这里 \(g:kY\to kZ\)，\(f:kX\to kY\)，故 \(g\circ f:kX\to kZ\)。

证明 \(c_{X,Y,Z}\) 连续。考虑映射
\[
\widetilde c:
M(Y,Z)\times_k M(X,Y)\times_k X\to kZ,
\qquad
\widetilde c(g,f,x)=g(f(x)).
\]
它可分解为连续映射的复合：
\[
M(Y,Z)\times M(X,Y)\times X
\xrightarrow{\ \mathrm{id}\times e_{X,Y}\ }
M(Y,Z)\times kY
\xrightarrow{\ e_{Y,Z}\ }kZ,
\]
其中 \(e_{A,B}\) 是 \(\mathbf{CGH}\) 中的求值映射。由 \(\mathbf{CGH}\) 的指数律，\(\widetilde c\) 的指数转置
\[
M(Y,Z)\times_k M(X,Y)\to [X,kZ]=M(X,Z)
\]
连续；它正好就是 \(c_{X,Y,Z}\)。

### 2. 结合律

记
\[
c_{A,B,C}:M(B,C)\times_k M(A,B)\to M(A,C),
\qquad c_{A,B,C}(g,f)=g\circ f.
\]
对
\[
h\in M(Z,W),\quad g\in M(Y,Z),\quad f\in M(X,Y),
\]
有逐点等式
\[
c_{X,Z,W}\bigl(c_{Y,Z,W}(h,g),f\bigr)
=h\circ g\circ f
=
c_{X,Y,W}\bigl(h,c_{X,Y,Z}(g,f)\bigr).
\]
因此下图在通常的 k-积结合同胚下交换：
\[
\begin{array}{ccc}
M(Z,W)\times M(Y,Z)\times M(X,Y)
&\xrightarrow{\ c_{Y,Z,W}\times \mathrm{id}\ }
&M(Y,W)\times M(X,Y)\\
\Big\downarrow{\mathrm{id}\times c_{X,Y,Z}}
&&\Big\downarrow{c_{X,Y,W}}\\
M(Z,W)\times M(X,Z)
&\xrightarrow{\ c_{X,Z,W}\ }
&M(X,W).
\end{array}
\]
即复合满足结合律。

### 3. 单位律

对每个 \(X\)，令
\[
u_X:*\to M(X,X),\qquad u_X(*)=\mathrm{id}_{kX}.
\]
由于定义域是单点空间，\(u_X\) 连续。于是有恒等律：
\[
c_{X,X,Y}\circ(\mathrm{id}_{M(X,Y)}\times u_X)
=\mathrm{id}_{M(X,Y)}
\]
（在 \(M(X,Y)\times *\cong M(X,Y)\) 下），以及
\[
c_{X,Y,Y}\circ(u_Y\times \mathrm{id}_{M(X,Y)})
=\mathrm{id}_{M(X,Y)}
\]
（在 \(*\times M(X,Y)\cong M(X,Y)\) 下）。逐点就是
\[
f\circ\mathrm{id}_{kX}=f,\qquad
\mathrm{id}_{kY}\circ f=f.
\]

### 4. \(h_f\) 为自然同构的充要条件

设 \(f:X\to Y\) 连续。结论：
\[
\boxed{
h_f:h_X\to h_Y\text{ 是自然同构}
\iff
kf:kX\to kY\text{ 是 homeomorphism（同胚）}.
}
\]
其中 \(kf\) 与 \(f\) 有同一底集映射。

证明：由 S2(b)，自然同构
\[
\operatorname{Nat}(h_X,h_Y)\cong C(kX,kY)
\]
在 \(X,Y\) 中自然；它将 \(h_f\) 送到 \(kf\)。因此 \(h_f\) 在函子范畴中可逆当且仅当 \(kf\) 在 \(\mathbf{CGH}\) 中可逆，即当且仅当 \(kf\) 是同胚。

等价地，也可以说：\(f\) 是双射，且
\[
f:(X,kX)\to(Y,kY)
\]
及其逆都连续。

### 5. 第一可数时能否升级为普通同胚

结论：\(\boxed{\text{能。}}\)

若 \(X,Y\) 第一可数 Hausdorff，由 S4 得
\[
kX=X,\qquad kY=Y.
\]
于是 \(kf=f\)。由上面的充要条件，
\[
h_f\text{ 自然同构}
\iff f:X\to Y\text{ 是同胚}.
\]
故在 \(X,Y\) 第一可数的情形，确实可以升级为原拓扑下的普通同胚。S5 的反例说明，去掉第一可数性（或更一般地，去掉适当的紧生成性条件）后不能这样升级。