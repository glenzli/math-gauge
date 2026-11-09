## 预备事实

设 \(X\) 为完备格，\(T:X\to X\) 单调。记
\[
\operatorname{Pre}(T)=\{x\in X:T(x)\le x\}
\]
为前不动点集。则 Knaster–Tarski 定理给出
\[
\mu T=\bigwedge \operatorname{Pre}(T),
\]
且 \(\mu T\) 是 \(T\) 的最小不动点，同时也是最小前不动点。证明如下：令 \(m=\bigwedge\operatorname{Pre}(T)\)。对任意 \(x\in\operatorname{Pre}(T)\)，有 \(m\le x\)，故
\[
T(m)\le T(x)\le x.
\]
于是 \(T(m)\le m\)，即 \(T(m)\in\operatorname{Pre}(T)\)，从而 \(m\le T(m)\)。故 \(T(m)=m\)。若 \(y\) 为任意不动点，则 \(m\le y\)，所以 \(m=\mu T\)。

此外，若 \(S,T:X\to X\) 单调且逐点 \(S\le T\)，则
\[
S(\mu T)\le T(\mu T)=\mu T,
\]
故 \(\mu T\) 是 \(S\) 的前不动点，从而 \(\mu S\le \mu T\)。后文反复使用这一比较原则。

---

## S1 参数与消元

设 \(x=(a,b,c)\in L=A\times B\times C\)，并写
\[
\Phi_p(x)=\bigl(F(p,x),G(p,x),H(p,x)\bigr).
\]
“联合单调”意味着：若 \(p\le q\) 且 \(x\le y\)，则
\[
\Phi_p(x)\le \Phi_q(y).
\]
特别地，对每个 \(p\)，\(\Phi_p:L\to L\) 单调。

### 1. 构造 \(\sigma\) 及其单调性

由 \(L\) 完备且 \(\Phi_p\) 单调，Knaster–Tarski 定理保证最小不动点存在。定义
\[
\sigma(p):=\mu\Phi_p
=\bigwedge\{x\in L:\Phi_p(x)\le x\}.
\]
若 \(p\le q\)，则对一切 \(x\in L\)，有 \(\Phi_p(x)\le\Phi_q(x)\)。由上面的比较原则，
\[
\sigma(p)=\mu\Phi_p\le \mu\Phi_q=\sigma(q).
\]
故 \(\sigma:P\to L\) 单调。

### 2. 单块消元引理

设 \(X,Y\) 为完备格，\(T:X\times Y\to X\times Y\) 单调。对 \(y\in Y\)，定义
\[
T_y:X\to X,\qquad T_y(x)=\pi_X T(x,y).
\]
令
\[
g(y)=\mu T_y,\qquad 
R(y)=\pi_Y T(g(y),y).
\]
则：

1. \(g(y)\) 良定义；
2. \(g:Y\to X\) 单调；
3. \(R:Y\to Y\) 单调；
4. 
\[
\mu T=(g(\mu R),\mu R).
\]

证明：对固定 \(y\)，\(T_y\) 是完备格 \(X\) 上的单调自映射，故 \(g(y)\) 存在。若 \(y\le y'\)，则对一切 \(x\)，
\[
T_y(x)=\pi_X T(x,y)\le \pi_X T(x,y')=T_{y'}(x),
\]
故 \(T_y\le T_{y'}\)，由比较原则得 \(g(y)\le g(y')\)。于是
\[
R(y)=\pi_Y T(g(y),y)
\le \pi_Y T(g(y'),y')=R(y'),
\]
所以 \(R\) 单调。

下面证明 \(\mu T=(g(\mu R),\mu R)\)。令
\[
w=(x,y)=\mu T.
\]
因为 \(w=T(w)\)，所以 \(x=T_y(x)\)，故 \(g(y)\le x\)。记 \(z=R(y)\)，则
\[
T(g(y),y)=(g(y),z).
\]
由于 \(g(y)\le x\)，有 \(T(g(y),y)\le w\)，特别地 \(z\le y\)。于是由单调性，
\[
T(g(y),z)\le T(g(y),y)=(g(y),z),
\]
即 \((g(y),z)\) 是 \(T\) 的前不动点。由 \(w\) 是最小前不动点，
\[
w\le (g(y),z),
\]
从而 \(x\le g(y)\) 且 \(y\le z\)。结合 \(g(y)\le x\)、\(z\le y\)，得
\[
x=g(y),\qquad z=y.
\]
故 \(y=R(y)\) 是 \(R\) 的不动点。若 \(t\) 是 \(R\) 的任意不动点，则 \((g(t),t)\) 是 \(T\) 的不动点，故 \(w\le(g(t),t)\)，从而 \(y\le t\)。因此 \(y=\mu R\)，且 \(x=g(\mu R)\)。引理得证。

若 \(T=T^p\) 还联合依赖于参数 \(p\)，则上述证明逐字给出：
\[
g(p,y)=\mu(T^p_y),\qquad 
R(p,y)=\pi_Y T^p(g(p,y),y)
\]
均联合单调，并且对每个 \(p\)，
\[
\mu T^p=(g(p,\mu R^p),\mu R^p).
\]

### 3. 任意分块与消元顺序

把 \(\{A,B,C\}\) 任意分成若干非空块，并按顺序
\[
B_1,B_2,\dots,B_k
\]
消元。记
\[
Z_j=\prod_{i=j+1}^k X_{B_i},
\qquad Z_0=L,\quad Z_k=\{\ast\}.
\]
这里 \(X_A=A,X_B=B,X_C=C\)。归纳定义约化系统 \(R_j^p:Z_j\to Z_j\)：

起点取
\[
R_0^p=\Phi_p.
\]
在第 \(j\) 步，把 \(z\in Z_{j-1}\) 写成
\[
z=(x,z'),\qquad x\in X_{B_j},\ z'\in Z_j.
\]
定义块内映射
\[
T_{j,p,z'}(x)=\pi_{B_j}R_{j-1}^p(x,z'),
\]
其最小不动点为
\[
g_j^p(z')=\mu T_{j,p,z'}.
\]
再定义约化系统
\[
R_j^p(z')
=\pi_{Z_j}R_{j-1}^p\bigl(g_j^p(z'),z'\bigr).
\]
由单块消元引理，\(g_j^p\) 和 \(R_j^p\) 都良定义，且联合单调于 \((p,z')\)。同时
\[
\mu R_{j-1}^p
=
\bigl(g_j^p(\mu R_j^p),\mu R_j^p\bigr).
\]
逐次展开，最后 \(Z_k=\{\ast\}\)，得
\[
x_{B_k}=g_k^p(\ast),\qquad
x_{B_j}=g_j^p(x_{B_{j+1}},\dots,x_{B_k})
\quad (j=1,\dots,k-1),
\]
并且
\[
\mu\Phi_p=(x_{B_1},\dots,x_{B_k}).
\]
这就是“逐块求最小解、代入、再逆向回代”的结果。

因为上述构造对任意有序分块都成立，所以任意变量分块和任意消元顺序都得到同一个 \(\sigma(p)=\mu\Phi_p\)。中间每个 \(g_j^p\) 都是其块内单调自映射的最小不动点，而约化系统 \(R_j^p\) 是完备格 \(Z_j\) 上的单调自映射，故均良定义；并且所有中间最小解和约化系统对 \(p\) 及尚未消去的变量都单调。

例如取单元素块顺序 \(A,B,C\)，便得到
\[
c^\ast=g_C^p(\ast),\qquad
b^\ast=g_B^p(c^\ast),\qquad
a^\ast=g_A^p(b^\ast,c^\ast),
\]
最终
\[
\sigma(p)=(a^\ast,b^\ast,c^\ast).
\]
若把 \(\{A,B\}\) 作为一个块先消去，则 \(g_{\{A,B\}}^p(c)\in A\times B\) 是块内最小解，结论完全相同。

---

## S2 伴随结构的精确传递

由伴随关系
\[
\alpha x\le y\iff x\le\gamma y
\]
可得
\[
\alpha\gamma y\le y,\qquad x\le\gamma\alpha x
\]
且 \(\alpha,\gamma\) 均单调。

固定 \(p\)，记
\[
T=\Phi_p,\qquad U=\Psi_p,\qquad x=\mu T=\sigma(p),\qquad y=\mu U.
\]
由 \(\alpha T=U\alpha\)，
\[
U(\alpha x)
=\alpha T(x)
=\alpha x,
\]
故 \(\alpha x\) 是 \(U\) 的不动点。由于 \(y=\mu U\) 是最小不动点，
\[
y\le \alpha x.
\]

另一方面，由 \(\alpha\gamma y\le y\) 及 \(U\) 单调，
\[
\alpha T(\gamma y)
=U(\alpha\gamma y)
\le U(y)=y.
\]
由伴随关系，
\[
T(\gamma y)\le \gamma y.
\]
于是 \(\gamma y\) 是 \(T\) 的前不动点，而 \(x=\mu T\) 是最小前不动点，故
\[
x\le \gamma y.
\]
再作用 \(\alpha\)，利用 \(\alpha\gamma y\le y\)，得
\[
\alpha x\le \alpha\gamma y\le y.
\]
结合 \(y\le\alpha x\)，得到
\[
\boxed{\alpha(\sigma(p))=\alpha(\mu\Phi_p)=\mu\Psi_p.}
\]

与 S1 的一致性如下：

1. S1 已证明：无论怎样分块、按什么顺序消元，最终都得到同一个 \(\sigma(p)\)。因此对任意消元过程，最后把 \(\alpha\) 作用到完整元组上，得到的都是同一个值 \(\mu\Psi_p\)，不会因消元顺序不同而改变。
2. 若把 S1 用于 \(\Psi\) 本身（取平凡的单块分块即可；若 \(M\) 有乘积分解，也可取任意分块），S1 给出的参数最小解正是 \(p\mapsto\mu\Psi_p\)。S2 的等式说明它恰好等于 \(\alpha\sigma\) 的参数映射。
3. S1 的参数单调性也与 S2 相符：若 \(p\le q\)，则 \(\sigma(p)\le\sigma(q)\)，故由 \(\alpha\) 单调，
\[
\alpha\sigma(p)\le\alpha\sigma(q).
\]
由已证等式，这正是
\[
\mu\Psi_p\le\mu\Psi_q,
\]
与 \(\Psi\) 的联合单调性及 S1 应用于 \(\Psi\) 所得的参数单调性完全一致。

---

## S3 单边更新关系

固定 \(p\)，记
\[
T=\Phi_p,\qquad U=\Psi_p.
\]
仍保留 \(\alpha\dashv\gamma\)。

### 情形一：只有 \(\alpha T\le U\alpha\)

结论：
\[
\boxed{\alpha(\mu T)\le \mu U,}
\]
等价地，由伴随关系，
\[
\boxed{\mu T\le \gamma(\mu U).}
\]

证明：令 \(y=\mu U\)。由 \(\alpha\gamma y\le y\) 和 \(\alpha T\le U\alpha\)，
\[
\alpha T(\gamma y)
\le U(\alpha\gamma y)
\le U(y)=y.
\]
由伴随关系，\(T(\gamma y)\le\gamma y\)。因此 \(\gamma y\) 是 \(T\) 的前不动点，故
\[
\mu T\le\gamma y=\gamma(\mu U).
\]
再作用 \(\alpha\)，得
\[
\alpha(\mu T)\le\alpha\gamma(\mu U)\le\mu U.
\]

### 情形二：只有 \(U\alpha\le\alpha T\)

结论：
\[
\boxed{\mu U\le\alpha(\mu T).}
\]

证明：令 \(x=\mu T\)。由 \(U\alpha\le\alpha T\) 和 \(T(x)=x\)，
\[
U(\alpha x)\le\alpha T(x)=\alpha x.
\]
故 \(\alpha x\) 是 \(U\) 的前不动点，而 \(\mu U\) 是最小前不动点，所以
\[
\mu U\le\alpha x=\alpha(\mu T).
\]

一般不能得到反向不等式。

### 严格有限例

#### 例 A：\(\alpha T\le U\alpha\) 严格成立

取
\[
L=\{0<1\},\qquad M=\{0<1<2\}.
\]
定义
\[
\alpha(0)=0,\quad \alpha(1)=1,
\]
并取右伴随
\[
\gamma(0)=0,\quad \gamma(1)=\gamma(2)=1.
\]
直接核验：当 \(y=0\) 时，两边都等价于 \(x=0\)；当 \(y=1,2\) 时，两边对所有 \(x\in L\) 都成立。因此 \(\alpha\dashv\gamma\)。

令
\[
T(0)=T(1)=1,
\]
\[
U(0)=1,\qquad U(1)=2,\qquad U(2)=2.
\]
二者单调。计算得
\[
\mu T=1,\qquad \mu U=2.
\]
于是
\[
\alpha(\mu T)=\alpha(1)=1<2=\mu U.
\]
同时
\[
(\alpha T)(0)=1=U(\alpha(0)),\qquad
(\alpha T)(1)=1<2=U(\alpha(1)).
\]
故 \(\alpha T\le U\alpha\) 严格成立。反向 \(U\alpha\le\alpha T\) 在 \(x=1\) 处失败，因为
\[
U(\alpha(1))=U(1)=2>1=(\alpha T)(1).
\]

#### 例 B：\(U\alpha\le\alpha T\) 严格成立

仍取
\[
L=\{0<1\},\qquad M=\{0<1<2\}.
\]
定义
\[
\alpha(0)=0,\qquad \alpha(1)=2,
\]
并取
\[
\gamma(0)=\gamma(1)=0,\qquad \gamma(2)=1.
\]
当 \(y=0,1\) 时，两边都等价于 \(x=0\)；当 \(y=2\) 时，两边对所有 \(x\) 都成立，故 \(\alpha\dashv\gamma\)。

令
\[
T\equiv 1,\qquad U\equiv 1.
\]
则
\[
\mu T=1,\qquad \mu U=1,\qquad
\alpha(\mu T)=\alpha(1)=2>1=\mu U.
\]
而
\[
(U\alpha)(0)=U(0)=1<2=(\alpha T)(0),
\]
\[
(U\alpha)(1)=U(2)=1<2=(\alpha T)(1),
\]
故 \(U\alpha\le\alpha T\) 严格成立。反向 \(\alpha T\le U\alpha\) 在 \(x=0\) 处失败。

最后注意：在第二种情形下，一般也不能推出 \(\gamma(\mu U)\le\mu T\)。例如取
\[
L=M=\{0<1<2\},
\]
\[
\alpha(0)=0,\quad \alpha(1)=\alpha(2)=1,
\]
\[
\gamma(0)=0,\quad \gamma(1)=\gamma(2)=2.
\]
则 \(\alpha\dashv\gamma\)。取
\[
T\equiv1,\qquad U(0)=U(1)=1,\quad U(2)=2.
\]
则
\[
\mu T=1,\qquad \mu U=1,\qquad \gamma(\mu U)=\gamma(1)=2>1=\mu T.
\]
但仍有 \(U\alpha\le\alpha T\)，且 \(\mu U=\alpha(\mu T)\)。

---

## S4 单调半共轭

结论：仅由 \(L,M\) 完备、\(T,U\) 单调、\(\alpha\) 单调且
\[
\alpha T=U\alpha
\]
**不能推出**
\[
\alpha(\mu T)=\mu U.
\]
但普遍成立的有向比较是
\[
\boxed{\mu U\le \alpha(\mu T).}
\]

证明：由 \(\alpha T=U\alpha\) 及 \(T(\mu T)=\mu T\)，
\[
U(\alpha(\mu T))
=\alpha(T(\mu T))
=\alpha(\mu T).
\]
故 \(\alpha(\mu T)\) 是 \(U\) 的不动点。由于 \(\mu U\) 是 \(U\) 的最小不动点，
\[
\mu U\le\alpha(\mu T).
\]

反例：取
\[
L=\{0<1\},\qquad M=\{0<1<2\}.
\]
定义
\[
\alpha(0)=1,\qquad \alpha(1)=2,
\]
\[
T(0)=T(1)=1,
\]
\[
U(0)=0,\qquad U(1)=U(2)=2.
\]
这些映射都单调。并且
\[
\alpha T(0)=\alpha(1)=2,\qquad
\alpha T(1)=\alpha(1)=2,
\]
而
\[
U\alpha(0)=U(1)=2,\qquad
U\alpha(1)=U(2)=2.
\]
故 \(\alpha T=U\alpha\)。但
\[
\mu T=1,\qquad \alpha(\mu T)=\alpha(1)=2,
\]
而
\[
\mu U=0.
\]
于是
\[
\mu U=0<2=\alpha(\mu T),
\]
精确等式不成立。

---

## S5 连续递推的传递

结论：在本阶段条件下，最小不动点可以精确传递：
\[
\boxed{\alpha(\mu T)=\mu U.}
\]

证明：令
\[
x_0=\bot_L,\qquad x_{n+1}=T(x_n).
\]
由 \(x_0\le x_1\) 及 \(T\) 单调，归纳得
\[
x_0\le x_1\le x_2\le\cdots.
\]
记
\[
x_\omega=\bigvee_{n<\omega}x_n.
\]
由于 \(T\) 保持递增 \(\omega\) 链的上确界，
\[
T(x_\omega)
=\bigvee_{n<\omega}T(x_n)
=\bigvee_{n<\omega}x_{n+1}
=x_\omega.
\]
若 \(z\) 是 \(T\) 的前不动点，即 \(T(z)\le z\)，则由 \(x_0=\bot_L\le z\) 及归纳可得
\[
x_{n+1}=T(x_n)\le T(z)\le z.
\]
故 \(x_\omega\le z\)。因此 \(x_\omega\) 是最小前不动点，即
\[
\mu T=x_\omega=\bigvee_{n<\omega}T^n(\bot_L).
\]

同理，
\[
\mu U=\bigvee_{n<\omega}U^n(\bot_M).
\]
令
\[
y_n=U^n(\bot_M).
\]
由 \(\alpha(\bot_L)=\bot_M\) 及 \(\alpha T=U\alpha\)，归纳得
\[
\alpha(x_0)=\bot_M=y_0,
\]
\[
\alpha(x_{n+1})
=\alpha(T(x_n))
=U(\alpha(x_n))
=U(y_n)
=y_{n+1}.
\]
因此 \(\alpha(x_n)=y_n\)。又因 \(\alpha\) 保持递增 \(\omega\) 链的上确界，
\[
\alpha(\mu T)
=\alpha\left(\bigvee_{n<\omega}x_n\right)
=\bigvee_{n<\omega}\alpha(x_n)
=\bigvee_{n<\omega}y_n
=\mu U.
\]
整个证明没有使用右伴随。

---

## S6 可数阶段与边界

### 1. \(x_\omega\) 是否必为 \(\mu T\)

设 \(L\) 完备，\(T:L\to L\) 仅单调，令
\[
x_n=T^n(\bot_L),\qquad 
x_\omega=\bigvee_{n<\omega}x_n.
\]
结论：\(x_\omega\) **不一定**等于 \(\mu T\)。

先注意两个普遍事实。

第一，对任意前不动点 \(z\)（即 \(T(z)\le z\)），由 \(\bot_L\le z\) 和单调性归纳得
\[
x_n\le z\qquad(n<\omega),
\]
故
\[
x_\omega\le z.
\]
特别地，
\[
x_\omega\le\mu T.
\]

第二，恒有
\[
x_\omega\le T(x_\omega).
\]
事实上，对每个 \(n\)，由 \(x_n\le x_\omega\) 得
\[
x_{n+1}=T(x_n)\le T(x_\omega),
\]
取上确界便得 \(x_\omega\le T(x_\omega)\)。

因此 \(x_\omega\) 已自动是“后不动点”；它成为 \(T\) 的不动点当且仅当 \(T(x_\omega)\le x_\omega\)。

### 2. 充要条件

\[
\boxed{x_\omega=\mu T
\iff T(x_\omega)\le x_\omega
\iff T(x_\omega)=x_\omega.}
\]

证明：若 \(T(x_\omega)\le x_\omega\)，则 \(x_\omega\) 是前不动点，故 \(\mu T\le x_\omega\)；而前面已有 \(x_\omega\le\mu T\)，故相等。反过来，若 \(x_\omega=\mu T\)，则 \(T(x_\omega)=x_\omega\)。

### 3. 条件失败的完整例子

取完备链
\[
L=\{\bot\}\cup\{a_n:n<\omega\}\cup\{\lambda\}\cup\{\top\},
\]
其序为
\[
\bot<a_0<a_1<\cdots<a_n<\cdots<\lambda<\top.
\]
这是完备链，因为 \(\{a_n\}\) 的上确界恰为 \(\lambda\)。

定义
\[
T(\bot)=a_0,
\]
\[
T(a_n)=a_{n+1}\qquad(n<\omega),
\]
\[
T(\lambda)=\top,\qquad T(\top)=\top.
\]
容易核验 \(T\) 单调：
\[
\bot<a_0\implies a_0<a_1,
\]
\[
a_n<a_{n+1}\implies a_{n+1}<a_{n+2},
\]
\[
a_n<\lambda\implies a_{n+1}<\top,
\]
\[
\lambda<\top\implies \top\le\top.
\]

迭代从 \(\bot\) 开始：
\[
T^0(\bot)=\bot,\quad
T^1(\bot)=a_0,\quad
T^2(\bot)=a_1,\quad\ldots,\quad
T^n(\bot)=a_{n-1}\quad(n\ge1).
\]
因此
\[
x_\omega
=\bigvee_{n<\omega}T^n(\bot)
=\bigvee_{n<\omega}a_n
=\lambda.
\]
但
\[
T(x_\omega)=T(\lambda)=\top>\lambda,
\]
故条件 \(T(x_\omega)\le x_\omega\) 失败。

再看最小不动点。\(T(\top)=\top\)，而
\[
T(\bot)=a_0\ne\bot,\qquad
T(a_n)=a_{n+1}\ne a_n,\qquad
T(\lambda)=\top\ne\lambda.
\]
所以 \(T\) 的唯一不动点是 \(\top\)，从而
\[
\mu T=\top.
\]
于是
\[
x_\omega=\lambda<\top=\mu T.
\]
这也说明 \(T\) 不保持递增 \(\omega\) 链 \(\{a_n\}\) 的上确界：
\[
\bigvee_{n<\omega}T(a_n)=\lambda,\qquad
T(\lambda)=\top.
\]

---

### 4. 精确传递的两个充分机制

以下两个机制都只是**充分条件**，不是必要条件。

#### 机制 I：右伴随机制

若 \(\alpha:L\to M\) 有右伴随 \(\gamma:M\to L\)，即
\[
\alpha\dashv\gamma,
\]
且
\[
\alpha T=U\alpha,
\]
则
\[
\boxed{\alpha(\mu T)=\mu U.}
\]
这正是 S2 的结论；对 S2 的参数版本则对每个 \(p\) 都有
\[
\alpha(\mu\Phi_p)=\mu\Psi_p.
\]
该机制不需要 \(T,U,\alpha\) 具有任何连续性。S4 说明：若去掉右伴随结构，仅保留单调半共轭 \(\alpha T=U\alpha\)，精确等式不保证成立。

#### 机制 II：可数连续性机制

若 \(T,U\) 都保持递增 \(\omega\) 链的上确界，\(\alpha\) 单调、保持递增 \(\omega\) 链的上确界，且
\[
\alpha(\bot_L)=\bot_M,\qquad \alpha T=U\alpha,
\]
则
\[
\boxed{\alpha(\mu T)=\mu U.}
\]
这正是 S5 的结论。该机制不需要 \(\alpha\) 有右伴随。

#### 它们不是必要条件

例如，机制 I 的右伴随条件不是必要的。取
\[
L=\mathcal P(\{a,b\}),\qquad M=\{0<1<2\},
\]
定义
\[
\alpha(S)=|S|.
\]
则 \(\alpha\) 单调，但不保持二元并：\(\alpha(\{a\}\cup\{b\})=2\)，而
\[
\alpha(\{a\})\vee\alpha(\{b\})=1\vee1=1.
\]
故 \(\alpha\) 没有右伴随。然而取 \(T=\operatorname{id}_L\)、\(U=\operatorname{id}_M\)，则
\[
\alpha T=U\alpha,\qquad
\mu T=\varnothing,\qquad
\mu U=0,
\]
从而
\[
\alpha(\mu T)=\alpha(\varnothing)=0=\mu U.
\]
所以即使没有右伴随，精确传递也可能偶然成立。

机制 II 的连续性条件也不是必要的。仍取 S6 上面的非连续例子中的 \(T\)，令
\[
M=L,\qquad U=T,\qquad \alpha=\operatorname{id}_L.
\]
则 \(\alpha T=U\alpha\)，且
\[
\alpha(\mu T)=\mu T=\mu U,
\]
但 \(T=U\) 不保持递增 \(\omega\) 链的上确界。因此连续性只是保证传递的充分机制，而不是精确传递的必要条件。

以上 S1–S6 已全部完成。