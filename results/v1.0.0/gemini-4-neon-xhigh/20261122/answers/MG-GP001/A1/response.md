下面按 S1–S6 逐项作答。记 $I=[0,1]$，几何实现均取通常的拓扑（对有限抽象单纯复形，其通常拓扑与标准单纯形弱拓扑及嵌入欧氏空间 $\mathbb{R}^{V(K)}$ 的子空间拓扑一致）。

---

## S1 可缩子复形的商

### 结论
商映射 $q\colon Y\to Y/A$ 是同伦等价。

### 证明

#### 步骤 1：商映射与 $I$ 的乘积仍为商映射（同伦下降的拓扑基础）
**辅助引理 1.1.** 设 $p\colon M\to N$ 是商映射，则 $p\times\mathrm{id}_I\colon M\times I\to N\times I$ 也是商映射。

*证明.* 设 $U\subseteq N\times I$ 满足 $\widetilde{U}:=(p\times\mathrm{id}_I)^{-1}(U)$ 在 $M\times I$ 中开，需证 $U$ 在 $N\times I$ 中开。任取 $(n_0,t_0)\in U$，取 $m_0\in M$ 使 $p(m_0)=n_0$，则 $(m_0,t_0)\in \widetilde{U}$。因 $\widetilde{U}$ 开，存在 $M$ 中含 $m_0$ 的开集 $V_0$ 与 $I$ 中含 $t_0$ 的开集 $J$ 使 $V_0\times J\subseteq \widetilde{U}$。因 $I=[0,1]$ 局部紧 Hausdorff，存在闭（从而紧）区间 $K\subseteq J$ 及 $I$ 中开邻域 $J'$ 使 $t_0\in J'\subseteq K\subseteq J$。令
$$W:=\{m\in M : \{m\}\times K\subseteq \widetilde{U}\}.$$
1. $m_0\in W$（因 $V_0\times K\subseteq V_0\times J\subseteq \widetilde{U}$）。
2. $W$ 在 $M$ 中开：对任意 $m\in W$，由 $\{m\}\times K\subseteq \widetilde{U}$ 与 $K$ 的紧性（管状引理），存在 $m$ 的开邻域 $V\subseteq M$ 使 $V\times K\subseteq \widetilde{U}$，即 $V\subseteq W$。
3. $W$ 关于 $p$ 饱和：若 $p(m)=p(m')$ 且 $m\in W$，则对一切 $t\in K$ 有 $(p(m'),t)=(p(m),t)\in U$，故 $(m',t)\in\widetilde{U}$，即 $m'\in W$。

由 $p$ 是商映射且 $p^{-1}(p(W))=W$ 开，知 $p(W)$ 在 $N$ 中开。于是 $p(W)\times J'$ 是 $(n_0,t_0)$ 在 $N\times I$ 中的开邻域，且对任意 $(p(m),t)\in p(W)\times J'$（其中 $m\in W,t\in J'\subseteq K$），有 $(m,t)\in\widetilde{U}$，故 $(p(m),t)\in U$。从而 $U$ 开，$p\times\mathrm{id}_I$ 是商映射。$\square$

*(注：在本题中 $Y$ 为有限 CW 复形，故 $Y$ 紧 Hausdorff（从而正规），子复形 $A$ 闭，易验证 $Y/A$ 亦紧 Hausdorff；因而 $q\times\mathrm{id}_I\colon Y\times I\to (Y/A)\times I$ 是紧空间到 Hausdorff 空间的连续满射，自动为闭映射，从而也是商映射。辅助引理 1.1 在不假定紧性时同样有效，下文单胞腔粘接处也需用到。)*

---

#### 步骤 2：有限 CW 对 $(Y,A)$ 满足同伦扩张性质（HEP）
先证对任意 $n\ge 0$，存在连续收缩映射 $r_n\colon D^n\times I\to (D^n\times\{0\})\cup(\partial D^n\times I)$：
- $n=0$ 时 $\partial D^0=\emptyset$，取 $r_0(x,t)=(x,0)$。
- $n\ge 1$ 时（取 $D^n=\{x\in\mathbb{R}^n:\|x\|\le 1\}$），从 $\mathbb{R}^n\times\mathbb{R}$ 中的点 $(0,2)$ 作径向投影，显式定义
$$r_n(x,t)=\begin{cases}
\left(\dfrac{2}{2-t}x,\;0\right), & t\le 2(1-\|x\|),\\[6pt]
\left(\dfrac{x}{\|x\|},\;2-\dfrac{2-t}{\|x\|}\right), & t\ge 2(1-\|x\|).
\end{cases}$$
检验：当 $t\le 2(1-\|x\|)$ 时有 $2-t\ge 1>0$ 且 $\frac{2\|x\|}{2-t}\le 1$；当 $t\ge 2(1-\|x\|)$ 时有 $\|x\|\ge 1-\frac{t}{2}\ge\frac{1}{2}>0$ 且 $0\le 2-\frac{2-t}{\|x\|}\le t\le 1$；在公共闭集 $t=2(1-\|x\|)$ 上两式均给出 $(\frac{x}{\|x\|},0)$。由粘贴引理 $r_n$ 连续，且在 $t=0$ 与 $\|x\|=1$ 上均为恒等映射。

对单胞腔粘接 $Z'=Z\cup_\varphi D^n$（其中 $\varphi\colon \partial D^n\to Z$ 为粘接映射，商映射为 $p\colon Z\sqcup D^n\to Z'$），若给定连续映射 $f\colon Z'\to W$ 及同伦 $h\colon Z\times I\to W$ 满足 $h(-,0)=f|_Z$，则 $f\circ p|_{D^n}$ 与 $h\circ(\varphi\times\mathrm{id}_I)$ 在 $(D^n\times\{0\})\cup(\partial D^n\times I)$ 上粘贴为连续映射，与 $r_n$ 复合得到 $D^n\times I\to W$；再与 $h\colon Z\times I\to W$ 合并为 $(Z\sqcup D^n)\times I\to W$，且在粘接关系上相容。由辅助引理 1.1，$p\times\mathrm{id}_I\colon (Z\sqcup D^n)\times I\to Z'\times I$ 是商映射，故该映射连续下降到 $Z'\times I\to W$。

因 $Y$ 是有限 CW 复形、$A\subseteq Y$ 是子复形，$Y$ 可由 $A$ 出发按维数非降顺序经有限次粘接胞腔得到；由有限归纳法，$(Y,A)$ 具有同伦扩张性质（HEP）。

---

#### 步骤 3：构造同伦逆并证明同伦能下降到商
因 $A$ 非空可缩，取 $a_0\in A$ 及连续同伦 $h\colon A\times I\to A$ 满足
$$h(a,0)=a,\qquad h(a,1)=a_0\qquad (\forall a\in A).$$
记包含映射为 $i\colon A\hookrightarrow Y$。对 $\mathrm{id}_Y\colon Y\to Y$ 及同伦 $i\circ h\colon A\times I\to Y$（满足 $(i\circ h)(a,0)=a=\mathrm{id}_Y(a)$），由 $(Y,A)$ 的 HEP 得连续同伦 $F\colon Y\times I\to Y$ 满足：
1. $F(y,0)=y$（$\forall y\in Y$）；
2. $F(a,t)=h(a,t)\in A$（$\forall a\in A,\;\forall t\in I$）；
3. 特别地，$f_1:=F(-,1)\colon Y\to Y$ 满足 $f_1(A)=\{a_0\}$。

因 $f_1$ 在 $A$ 上取常值 $a_0$，在商映射 $q\colon Y\to Y/A$ 的每条纤维上均取常值，由商拓扑的泛性质存在唯一连续映射 $g\colon Y/A\to Y$ 满足 $g\circ q=f_1$。

1. **$g\circ q\simeq \mathrm{id}_Y$**：由 $F\colon Y\times I\to Y$ 即给出 $\mathrm{id}_Y=F(-,0)\simeq F(-,1)=f_1=g\circ q$。
2. **$q\circ g\simeq \mathrm{id}_{Y/A}$ 及同伦为何能下降到商**：考虑连续映射 $q\circ F\colon Y\times I\to Y/A$。它能下降为连续同伦 $\overline{F}\colon (Y/A)\times I\to Y/A$ 源于以下两点：
   - **集合论相容性（纤维上常值）**：由于 $F|_{A\times I}=h$ 取值仍在 $A$ 中（即 $F(A\times I)\subseteq A$），对任意 $t\in I$ 与任意 $a\in A$ 均有 $(q\circ F)(a,t)=q(h(a,t))=*$（其中 $*=q(A)$ 为 $A$ 坍缩成的点）。因此若 $(q\times\mathrm{id}_I)(y,t)=(q\times\mathrm{id}_I)(y',t')$，则必有 $t=t'$ 且要么 $y=y'$、要么 $y,y'\in A$，两种情形下都有 $(q\circ F)(y,t)=(q\circ F)(y',t')$。故存在唯一的集合映射 $\overline{F}\colon (Y/A)\times I\to Y/A$ 满足 $\overline{F}\circ(q\times\mathrm{id}_I)=q\circ F$。
   - **拓扑相容性（商映射与 $I$ 乘积保持商映射性）**：由辅助引理 1.1（或有限 CW 情形下 $Y\times I$ 紧、$(Y/A)\times I$ Hausdorff），$q\times\mathrm{id}_I\colon Y\times I\to (Y/A)\times I$ 是商映射。由商拓扑的泛性质，$\overline{F}$ 连续。

   检验端点：对任意 $y\in Y$，
   $$\overline{F}(q(y),0)=q(F(y,0))=q(y)=\mathrm{id}_{Y/A}(q(y)),$$
   $$\overline{F}(q(y),1)=q(F(y,1))=q(f_1(y))=q(g(q(y)))=(q\circ g)(q(y)).$$
   因 $q$ 满射，故 $\overline{F}(-,0)=\mathrm{id}_{Y/A}$ 且 $\overline{F}(-,1)=q\circ g$，从而 $q\circ g\simeq\mathrm{id}_{Y/A}$。

综上，$q\colon Y\to Y/A$ 是同伦等价。$\square$

---

## S2 非可缩底空间上的锥附着

### 约定与结论
取锥 $CL=(L\times I)/(L\times\{1\})$，商映射 $\pi\colon L\times I\to CL$，锥顶 $c_+=\pi(L\times\{1\})$，将 $L$ 通过 $x\mapsto\pi(x,0)$ 视为 $CL$ 的底子空间。于是
$$Y=D\cup_i CL=(D\sqcup CL)/(\pi(x,0)\sim i(x),\;\forall x\in L),$$
其中 $i\colon L\hookrightarrow D$ 为包含映射。取非约化悬挂
$$\Sigma L=(L\times I)/(L\times\{0\}\sim s_-,\; L\times\{1\}\sim s_+)\cong CL/\pi(L\times\{0\}),$$
其中 $s_-=[L\times\{0\}],\,s_+=[L\times\{1\}]$ 为南北两极。我们将证明：对任取点 $d_0\in D$，均有
$$Y\simeq D\vee_{d_0\sim s_-}\Sigma L,$$
并进一步说明楔点的选择（在 $D\times\Sigma L$ 中任选楔点均给出相同同伦型）。

### 证明

#### 步骤 1：选取目标点 $d_0\in D$ 与零伦 $H$
已知 $i\colon L\hookrightarrow D$ 零伦，故存在 $d_1\in D$ 及同伦 $H_0\colon L\times I\to D$ 使 $H_0(x,0)=i(x),\,H_0(x,1)=d_1$。任取 $d_0\in D$，因 $D$ 路径连通，存在路径 $\gamma\colon I\to D$ 使 $\gamma(0)=d_1,\gamma(1)=d_0$。拼接得连续同伦 $H\colon L\times I\to D$：
$$H(x,t)=\begin{cases} H_0(x,2t), & 0\le t\le \tfrac{1}{2},\\ \gamma(2t-1), & \tfrac{1}{2}\le t\le 1, \end{cases}$$
满足 $H(x,0)=i(x)$ 且 $H(x,1)=c_{d_0}(x):=d_0$（常值映射）。

#### 步骤 2：构造中间空间 $M$ 并证明 $D\cup_i CL\simeq M\simeq D\cup_{c_{d_0}} CL$
构造商空间
$$M:=D\cup_H (CL\times I)=(D\sqcup (CL\times I))\big/\big((\pi(x,0),t)\sim H(x,t),\;\forall x\in L,t\in I\big),$$
记商映射为 $q_M\colon D\sqcup (CL\times I)\to M$，记 $q_0\colon D\sqcup CL\to D\cup_i CL$ 为 $Y=D\cup_i CL$ 的商映射。

在正方形 $[0,1]_u\times [0,1]_t$ 上定义从点 $(1,2)$ 出发的径向收缩 $r\colon [0,1]^2\to (\{t=0\}\cup\{u=0\})$：
$$r(u,t)=\begin{cases}
\left(\dfrac{2u-t}{2-t},\;0\right), & t\le 2u,\\[6pt]
\left(0,\;\dfrac{t-2u}{1-u}\right), & t\ge 2u.
\end{cases}$$
检验：
- 在 $A_1=\{(u,t):t\le 2u\}$ 上，$2-t\ge 1>0$ 且 $0\le 2u-t\le 2-t$；
- 在 $A_2=\{(u,t):t\ge 2u\}$ 上，$u\le t/2\le 1/2$ 故 $1-u\ge 1/2>0$，且 $0\le t-2u\le 1-u$；
- 在交集 $t=2u$ 上两式均为 $(0,0)$；由粘贴引理 $r$ 连续；
- 在 $t=0$ 上 $r(u,0)=(u,0)$；在 $u=0$ 上 $r(0,t)=(0,t)$；
- 关键性质：在顶边 $u=1$ 上恒有 $t\le 1<2=2u$，故 $r(1,t)=(1,0)$。

令线性同伦 $r_s(u,t)=(u_s(u,t),t_s(u,t)):=(1-s)(u,t)+s\,r(u,t)$（$s\in I$）。于是：
- $r_s(u,0)=(u,0)$，$r_s(0,t)=(0,t)$；
- $r_s(1,t)=(1,(1-s)t)$，即 $u=1$ 时第一坐标恒为 $1$！

因 $\pi\colon L\times I\to CL$ 是商映射且 $I\times I$ 局部紧 Hausdorff，对 $I$ 连续两次应用 S1 的辅助引理 1.1 知 $\pi\times\mathrm{id}_{I\times I}\colon (L\times I)\times I\times I\to (CL\times I)\times I$ 是商映射。定义
$$\widetilde{R}((x,u),t,s):=(\pi(x,u_s(u,t)),\;t_s(u,t))\in CL\times I.$$
当 $u=1$ 时 $u_s(1,t)=1$，故 $\widetilde{R}((x,1),t,s)=(c_+,(1-s)t)$ 与 $x$ 无关；从而 $\widetilde{R}$ 连续下降为 $R\colon (CL\times I)\times I\to CL\times I$。

再在 $(D\sqcup(CL\times I))\times I\to M$ 上定义 $\widetilde{\Phi}(d,s)=q_M(d)$ 与 $\widetilde{\Phi}(z,t,s)=q_M(R(z,t,s))$。当 $z=\pi(x,0)$ 时 $R(\pi(x,0),t,s)=(\pi(x,0),t)$，故
$$\widetilde{\Phi}(\pi(x,0),t,s)=q_M(\pi(x,0),t)=q_M(H(x,t))=\widetilde{\Phi}(H(x,t),s).$$
由辅助引理 1.1，$q_M\times\mathrm{id}_I$ 是商映射，故 $\widetilde{\Phi}$ 连续下降为同伦 $\Phi\colon M\times I\to M$，且 $\Phi(-,0)=\mathrm{id}_M$。

现在定义一对映射 $j_0\colon D\cup_i CL\to M$ 与 $\rho_0\colon M\to D\cup_i CL$：
- $j_0(q_0(d))=q_M(d)$（$d\in D$），$j_0(q_0(z))=q_M(z,0)$（$z\in CL$）。因 $q_M(\pi(x,0),0)=q_M(H(x,0))=q_M(i(x))$，$j_0$ 良定义且连续。
- 为构造 $\rho_0$，先定义 $\widetilde{\psi}\colon (L\times I)\times I\to D\cup_i CL$ 为
$$\widetilde{\psi}((x,u),t)=\begin{cases}
q_0\left(\pi\!\left(x,\dfrac{2u-t}{2-t}\right)\right), & t\le 2u,\\[6pt]
q_0\left(H\!\left(x,\dfrac{t-2u}{1-u}\right)\right), & t\ge 2u.
\end{cases}$$
在 $t=2u$ 上两式分别为 $q_0(\pi(x,0))$ 与 $q_0(H(x,0))=q_0(i(x))=q_0(\pi(x,0))$，故 $\widetilde{\psi}$ 连续；当 $u=1$ 时 $t\le 1<2u$，给出 $q_0(\pi(x,1))=q_0(c_+)$ 与 $x$ 无关，由 $\pi\times\mathrm{id}_I$ 是商映射（辅助引理 1.1）得连续映射 $\psi_1\colon CL\times I\to D\cup_i CL$。合并 $\psi_0=q_0|_D\colon D\to D\cup_i CL$ 与 $\psi_1$，在粘接点 $(\pi(x,0),t)\sim H(x,t)$ 处因 $u=0\implies t\ge 2u$，有 $\psi_1(\pi(x,0),t)=q_0(H(x,t))=\psi_0(H(x,t))$，故连续下降为 $\rho_0\colon M\to D\cup_i CL$。

直接检验复合：
- 对 $d\in D$：$\rho_0(j_0(q_0(d)))=q_0(d)$；对 $\pi(x,u)\in CL$：$t=0\le 2u$，故 $\rho_0(j_0(q_0(\pi(x,u))))=\rho_0(q_M(\pi(x,u),0))=q_0(\pi(x,u))$。因此 $\rho_0\circ j_0=\mathrm{id}_{D\cup_i CL}$。
- 对 $d\in D$：$j_0(\rho_0(q_M(d)))=q_M(d)=\Phi(q_M(d),1)$；
  当 $t\le 2u$ 时，$j_0(\rho_0(q_M(\pi(x,u),t)))=q_M(\pi(x,\frac{2u-t}{2-t}),0)=\Phi(q_M(\pi(x,u),t),1)$；
  当 $t\ge 2u$ 时，$j_0(\rho_0(q_M(\pi(x,u),t)))=q_M(H(x,\frac{t-2u}{1-u}))=q_M(\pi(x,0),\frac{t-2u}{1-u})=\Phi(q_M(\pi(x,u),t),1)$。
  因此 $j_0\circ \rho_0=\Phi(-,1)\simeq\Phi(-,0)=\mathrm{id}_M$。

从而 $j_0\colon D\cup_i CL\to M$ 是同伦等价。将参数 $t$ 替换为 $1-t$（等价于将 $H(x,t)$ 换为 $\overline{H}(x,t)=H(x,1-t)$），完全对称地得到 $j_1\colon D\cup_{c_{d_0}} CL\to M$ 也是同伦等价。因此
$$Y=D\cup_i CL\;\simeq\;M\;\simeq\;D\cup_{c_{d_0}} CL.$$

#### 步骤 3：识别 $D\cup_{c_{d_0}} CL\cong D\vee_{d_0\sim s_-}\Sigma L$
考察自然满射链
$$D\sqcup CL \xrightarrow{\;\mathrm{id}_D\sqcup\, p_\Sigma\;} D\sqcup \Sigma L \xrightarrow{\;p_\vee\;} D\vee_{d_0\sim s_-}\Sigma L,$$
其中 $p_\Sigma\colon CL\to CL/\pi(L\times\{0\})=\Sigma L$ 坍缩底面 $L\times\{0\}$ 为 $s_-$，$p_\vee$ 粘合 $d_0\sim s_-$。两者均为商映射，故复合映射也是商映射；其诱导的等价关系恰将 $CL$ 中全部 $\pi(x,0)$（$x\in L$）粘合到 $d_0\in D$（因 $L\neq\emptyset$，等价类由 $\pi(x,0)\sim d_0$ 生成），与 $D\cup_{c_{d_0}} CL$ 作为 $D\sqcup CL$ 的商空间所用的等价关系完全一致。由商拓扑的唯一性，得典范同胚
$$D\cup_{c_{d_0}} CL\cong D\vee_{d_0\sim s_-}\Sigma L.$$
综合步骤 2 与步骤 3，即证 $Y\simeq D\vee_{d_0\sim s_-}\Sigma L$。

---

#### 步骤 4：关于楔点选择的说明
1. **证明直接给出的自然楔点**：上述构造中，$\Sigma L$ 上的楔点自然取为悬挂的南极 $s_-=[L\times\{0\}]$（由翻转 $u\mapsto 1-u$ 对称性，取北极 $s_+$ 同胚等价）；$D$ 上的楔点 $d_0$ 为零伦 $H$ 的终点，因 $D$ **路径连通**，$d_0$ 可任意选取为 $D$ 的任何一点（例如任一 $0$-胞腔）。*(注：若 $D$ 不路径连通，则零伦终点 $d_0$ 必须位于包含 $L$ 的那个路径连通分支中，把 $\Sigma L$ 楔到另一分支可能改变同伦型。)*
2. **楔点在 $D\times\Sigma L$ 中任意选取均不改变同伦型**：事实上，对任意 $d_0,d_1\in D$ 及任意 $p,p'\in\Sigma L$，均有 $D\vee_{d_0\sim p}\Sigma L\simeq D\vee_{d_1\sim p'}\Sigma L$。证明如下：
   - **$\Sigma L$ 是路径连通有限 CW 复形**：因 $L$ 非空，对任意 $[x,u]\in\Sigma L$，路径 $\tau\mapsto [x,(1-\tau)u]$ 将其连至 $s_-$，故 $\Sigma L$ 路径连通；其有限 CW 结构由两个 $0$-胞腔 $s_-,s_+$ 及 $L$ 的每个 $k$-胞腔 $e^k$ 对应的 $(k+1)$-胞腔 $e^k\times(0,1)$ 组成。
   - **有限 CW 复形中任意一点均良基点化（即 $(Z,\{z\})$ 满足 HEP）**：设 $Z$ 为有限 CW 复形，$z\in Z$ 落在唯一开胞腔 $e^k$ 内。若 $k=0$ 则 $\{z\}$ 为子复形，$(Z,\{z\})$ 为 CW 对从而满足 HEP。若 $k\ge 1$，记 $Z^k=Z_0\cup_\varphi D^k$（$Z_0$ 为 $Z^k$ 去掉开胞腔 $e^k$ 的有限子复形），$z=\Phi(z_0)$（$z_0\in\operatorname{int}(D^k)$）。通过径向同胚 $(D^k,z_0)\cong (D^k,0)$ 将 $z_0$ 移至原点 $0$。在 $[0,1]_r\times[0,1]_t$ 上定义从 $(1/2,2)$ 出发的径向收缩 $\rho\colon [0,1]^2\to (\{t=0\}\cup\{r=0\}\cup\{r=1\})$：
     $$\rho(r,t)=\begin{cases}
     \left(0,\;\dfrac{t-4r}{1-2r}\right), & t\ge 4r,\\[6pt]
     \left(1,\;\dfrac{t-4(1-r)}{2r-1}\right), & t\ge 4(1-r),\\[6pt]
     \left(\dfrac{4r-t}{2(2-t)},\;0\right), & t\le \min(4r,\,4(1-r)).
     \end{cases}$$
     三闭区域覆盖 $[0,1]^2$ 且在公共边界 $t=4r$ 与 $t=4(1-r)$ 上分别一致给出 $(0,0)$ 与 $(1,0)$；而且当 $r\le 1/2$ 时其第一坐标满足 $0\le r'\le r$，故在 $D^k\times I$ 上定义 $\tilde{\rho}(x,t)=(\frac{r'}{\|x\|}x,t')$（$x\neq 0$）与 $\tilde{\rho}(0,t)=(0,t)$ 给出连续收缩 $D^k\times I\to (D^k\times\{0\})\cup((\partial D^k\cup\{0\})\times I)$。于是给定 $f\colon Z\to W$ 及 $h\colon\{z\}\times I\to W$（$h(z,0)=f(z)$），因 $Z_0$ 闭且 $z\notin Z_0$，可在 $(Z_0\cup\{z\})\times I=(Z_0\times I)\sqcup(\{z\}\times I)$ 上令 $Z_0\times I$ 取常值同伦 $f|_{Z_0}$，经 $\tilde{\rho}$ 延拓至 $Z^k\times I$，再由有限 CW 对 $(Z,Z^k)$ 的 HEP 延拓至 $Z\times I$。
   - **通过连接区间比较不同楔点**：对任意 $(d,p)\in D\times\Sigma L$，令 $Z(d,p)=(D\sqcup I\sqcup\Sigma L)/(0\sim d,\;1\sim p)$。因 $(D,\{d\})$ 与 $(\Sigma L,\{p\})$ 均满足 HEP，给定 $I\times I\to W$ 时可分别在 $D$ 与 $\Sigma L$ 上延拓两端点的同伦并经辅助引理 1.1 粘贴到 $Z(d,p)\times I$，故 $(Z(d,p),I)$ 满足 HEP；因 $I$ 可缩，完全仿照 S1 步骤 3 知 $Z(d,p)\to Z(d,p)/I\cong D\vee_{d\sim p}\Sigma L$ 是同伦等价。又因 $D$ 与 $\Sigma L$ 均路径连通，可将粘接映射 $\partial I=\{0,1\}\to D\sqcup\Sigma L$（$0\mapsto d_0,1\mapsto p$）同伦到 $(0\mapsto d_1,1\mapsto p')$；利用 S1 中 $r_1\colon D^1\times I\to (D^1\times\{0\})\cup(\partial D^1\times I)$ 与本节步骤 2 相同的中间空间构造，得 $Z(d_0,p)\simeq Z(d_1,p')$。从而
     $$D\vee_{d_0\sim p}\Sigma L\simeq Z(d_0,p)\simeq Z(d_1,p')\simeq D\vee_{d_1\sim p'}\Sigma L.$$

因此，在 $D$ 与 $\Sigma L$ 上任选楔点均得到同一同伦型。$\square$

---

## S3 整数扭结的实例

### 一般引理（供 S3、S4、S5 共用）
设 $K$ 是有限抽象单纯复形（此处约定抽象单纯复形的单形为非空有限顶点集，对取非空子集封闭），$v\in V(K)$ 为其顶点。记：
- 删除子复形 $K\setminus v:=\{\sigma\in K : v\notin\sigma\}$；
- 闭星 $\operatorname{st}_K(v):=\{\sigma\in K : \sigma\cup\{v\}\in K\}$；
- 链环 $\operatorname{lk}_K(v):=\{\sigma\in K : v\notin\sigma\text{ 且 }\sigma\cup\{v\}\in K\}$。

**引理 3.1.** 设 $K$ 有限、$v\in V(K)$，则 $|K\setminus v|$ 是 $|K|\setminus\{v\}$ 的强形变收缩核。

*证明.* 将 $|K|$ 标准仿射嵌入 $\mathbb{R}^{V(K)}$（顶点 $w$ 对应标准基向量 $e_w$），点 $x=\sum_{w}\lambda_w(x)e_w\in |K|$ 的重心坐标 $\lambda_w\colon |K|\to [0,1]$ 连续，且 $|K|\setminus\{v\}=\{x\in|K|:\lambda_v(x)<1\}$。在 $|K|\setminus\{v\}$ 上定义连续映射
$$r(x):=\frac{x-\lambda_v(x)e_v}{1-\lambda_v(x)},\qquad H(x,t):=(1-t)x+t\,r(x)\quad (t\in I).$$
对任意 $x\in|K|\setminus\{v\}$，记其承载单形 $\sigma=\{w:\lambda_w(x)>0\}\in K$。因 $\lambda_v(x)<1$，$\tau:=\sigma\setminus\{v\}$ 非空且 $\tau\in K\setminus v$。$r(x)$ 的非零坐标支撑恰为 $\tau$ 且坐标非负、和为 $1$，故 $r(x)\in|\tau|\subseteq|K\setminus v|$。因 $x,r(x)\in|\sigma|$ 且 $|\sigma|$ 凸，故 $H(x,t)\in|\sigma|\subseteq|K|$，且其 $v$-坐标为 $(1-t)\lambda_v(x)<1$，故 $H(x,t)\in|K|\setminus\{v\}$。显然 $H(x,0)=x$，$H(x,1)=r(x)\in|K\setminus v|$，且对 $x\in|K\setminus v|$ 有 $\lambda_v(x)=0\implies r(x)=x\implies H(x,t)=x$。$\square$

**引理 3.2（悬挂同调同构）.** 对任意非空拓扑空间 $Y$ 及系数环 $R\in\{\mathbb{Z},\mathbb{Q}\}$：
$$\widetilde{H}_0(\Sigma Y;R)=0,\qquad \widetilde{H}_{n+1}(\Sigma Y;R)\cong \widetilde{H}_n(Y;R)\quad (\forall n\ge 0).$$

*证明.* 记 $U=\Sigma Y\setminus\{s_-\}$，$V=\Sigma Y\setminus\{s_+\}$。则 $U,V$ 为 $\Sigma Y$ 的开子集且 $U\cup V=\Sigma Y$；$U$ 经 $([y,u],\tau)\mapsto [y,(1-\tau)u+\tau]$ 可缩至 $s_+$，$V$ 经 $([y,u],\tau)\mapsto [y,(1-\tau)u]$ 可缩至 $s_-$；且 $U\cap V\cong Y\times(0,1)\simeq Y$ **非空**（因 $Y\neq\emptyset$）。因而约化奇异同调的 **Mayer–Vietoris 长正合列** 适用：
$$\cdots\to \widetilde{H}_{n+1}(U;R)\oplus \widetilde{H}_{n+1}(V;R)\to \widetilde{H}_{n+1}(\Sigma Y;R)\xrightarrow{\partial}\widetilde{H}_n(U\cap V;R)\to \widetilde{H}_n(U;R)\oplus\widetilde{H}_n(V;R)\to\cdots$$
因 $U,V$ 可缩，对所有 $k\ge 0$ 有 $\widetilde{H}_k(U;R)=\widetilde{H}_k(V;R)=0$。故对一切 $n\ge 0$ 连接同态 $\partial$ 为同构，结合 $U\cap V\simeq Y$ 得 $\widetilde{H}_{n+1}(\Sigma Y;R)\cong\widetilde{H}_n(Y;R)$；且正合列末端给出 $\widetilde{H}_0(\Sigma Y;R)=0$。$\square$

---

### 构造
设 $L$ 为 $\mathbb{R}P^2$ 的任一有限抽象单纯三角剖分（$|L|\cong\mathbb{R}P^2$）。取两个不在 $V(L)$ 中的互异新顶点 $u,v$，构造**单纯悬挂**
$$K:=\{u,v\}*L = L\cup\{\{u\},\{v\}\}\cup\big\{\{u\}\cup\sigma,\;\{v\}\cup\sigma : \sigma\in L\big\},$$
其顶点集为 $V(K)=V(L)\sqcup\{u,v\}$。因 $|L|\cong\mathbb{R}P^2$ 非空，任取 $L$ 的一个顶点 $w\in V(L)$，令子复形为单条边
$$B:=\big\{\{v\},\;\{w\},\;\{v,w\}\big\}\subseteq K.$$

### 全部性质的验证
1. **$K$ 有限、$v\in V(K)$、$B\subseteq K$ 为含 $v$ 子复形**：由构造显然，且因 $\{w\}\in L$，有 $\{v,w\}\in K$，故 $B$ 为含 $v$ 子复形。
2. **$|K|\setminus\{v\}$ 非空可缩**：直接得 $K\setminus v=u*L$（以 $u$ 为锥顶的单纯锥）。$|u*L|$ 含 $e_u$ 故非空；又因 $u*L$ 中每个单形均包含在含 $u$ 的单形中，线性同伦 $(x,t)\mapsto (1-t)x+t e_u$ 在 $|u*L|$ 内将其收缩至 $e_u$，故 $|K\setminus v|$ 可缩。由引理 3.1，$|K|\setminus\{v\}$ 以 $|K\setminus v|$ 为强形变收缩核，从而 $|K|\setminus\{v\}$ 非空可缩。
3. **$(|B|\setminus\{v\})\hookrightarrow |B|$ 是同伦等价**：$|B|$ 为闭线段 $[e_w,e_v]$，$|B|\setminus\{v\}$ 为半开线段 $[e_w,e_v)$。令常值映射 $c_w\colon |B|\to |B|\setminus\{v\},\,x\mapsto e_w$，记包含为 $\iota\colon |B|\setminus\{v\}\hookrightarrow |B|$。线性同伦 $(x,t)\mapsto (1-t)x+te_w$ 同时将 $\iota\circ c_w$ 同伦于 $\mathrm{id}_{|B|}$、将 $c_w\circ \iota$ 同伦于 $\mathrm{id}_{|B|\setminus\{v\}}$（当 $x\in[e_w,e_v)$ 时 $\lambda_v((1-t)x+te_w)=(1-t)\lambda_v(x)<1$，故仍落于 $[e_w,e_v)$）。因此 $\iota$ 是同伦等价。
4. **$|K|\cong \Sigma|L|\cong \Sigma\mathbb{R}P^2$**：使用 $\Sigma|L|=(|L|\times[-1,1])/(|L|\times\{-1\},\,|L|\times\{1\})$，定义 $f\colon |L|\times[-1,1]\to |K|$：
   $$f(y,t)=\begin{cases} t e_v+(1-t)y, & t\in[0,1],\\ (-t)e_u+(1+t)y, & t\in[-1,0]. \end{cases}$$
   $f$ 连续，且把 $|L|\times\{1\}$ 映到 $e_v$、把 $|L|\times\{-1\}$ 映到 $e_u$，故诱导连续映射 $\bar{f}\colon \Sigma|L|\to |K|$。因 $\{u,v\}\notin K$，$|K|$ 中任意点 $x$ 的 $\lambda_u(x),\lambda_v(x)$ 不同时为正，故 $t=\lambda_v(x)-\lambda_u(x)\in[-1,1]$ 唯一确定，且当 $|t|<1$ 时 $y=\frac{x-\lambda_v(x)e_v-\lambda_u(x)e_u}{1-|t|}\in |L|$ 唯一确定；从而 $\bar{f}$ 为双射。因 $\Sigma|L|$ 紧、$|K|$ Hausdorff，$\bar{f}$ 是同胚。故 $|K|\cong \Sigma|L|\cong \Sigma\mathbb{R}P^2$。
5. **约化有理同调全零但 $|K|$ 不可缩**：
   $\mathbb{R}P^2=D^2/(z\sim -z\text{ on }S^1)$ 具有有限 CW 结构 $e^0\cup e^1\cup_\varphi e^2$，其中 $2$-胞腔粘接映射 $\varphi\colon S^1\to \mathbb{R}P^1\cong S^1$ 为 $z\mapsto z^2$（度数为 $2$）。因胞腔同调与奇异同调对有限 CW 复形自然同构，系数环 $R\in\{\mathbb{Z},\mathbb{Q}\}$ 上的胞腔链复形为
   $$0\longrightarrow R \xrightarrow{\;\times 2\;} R \xrightarrow{\;0\;} R \longrightarrow 0\qquad (\text{维数 }2,1,0).$$
   - 取 $R=\mathbb{Q}$：$\times 2\colon\mathbb{Q}\to\mathbb{Q}$ 是同构，故 $\widetilde{H}_n(\mathbb{R}P^2;\mathbb{Q})=0$（$\forall n\ge 0$）。由引理 3.2 及同调的同胚不变性，得
     $$\widetilde{H}_n(|K|;\mathbb{Q})\cong \widetilde{H}_n(\Sigma\mathbb{R}P^2;\mathbb{Q})=0\qquad (\forall n\ge 0).$$
   - 取 $R=\mathbb{Z}$：$\times 2\colon\mathbb{Z}\to\mathbb{Z}$ 单射且余核为 $\mathbb{Z}/2\mathbb{Z}$，故 $\widetilde{H}_1(\mathbb{R}P^2;\mathbb{Z})\cong\mathbb{Z}/2\mathbb{Z}$。由引理 3.2，
     $$\widetilde{H}_2(|K|;\mathbb{Z})\cong \widetilde{H}_2(\Sigma\mathbb{R}P^2;\mathbb{Z})\cong \widetilde{H}_1(\mathbb{R}P^2;\mathbb{Z})\cong \mathbb{Z}/2\mathbb{Z}\neq 0.$$
   因任意可缩空间的约化整系数奇异同调全零（同调的同伦不变性），故 $|K|$ **不可缩**。$\square$

---

## S4 整体对象与全部恢复目标

### 判定结论
**所列全部目标在给定条件下均成立**：
1. **可能同伦类型的完全刻画**：满足全部条件的三元组 $(K,v,B)$ 中，$X=|K|$ 可能的同伦类型**恰为所有非空有限抽象单纯复形 $L$ 的非约化悬挂 $\Sigma|L|$ 的同伦类型**（更具体地，对任意满足条件的三元组，必有 $\operatorname{lk}_K(v)\neq\emptyset$ 且 $X\simeq\Sigma|\operatorname{lk}_K(v)|$）。
2. **实现构造**：对任意非空有限抽象单纯复形 $L$，取 $K=\{u,v\}*L$（$u,v\notin V(L)$ 互异）及 $B=\{\{v\},\{w\},\{v,w\}\}$（$w\in V(L)$ 任取），即满足原全部条件且 $X=|K|\cong\Sigma|L|$。
3. **只用含 $v$ 单形及其面之间有限关联数据即可检验的 $X$ 可缩充要判据**：令 $L=\operatorname{lk}_K(v)=\{\sigma\setminus\{v\}:\sigma\in K,\,v\in\sigma,\,\sigma\neq\{v\}\}$（完全由含 $v$ 的单形及其面关联决定），记其维数为 $d=\dim L$，增广整系数单纯链复形为
   $$0\longrightarrow \widetilde{C}_d(L;\mathbb{Z})\xrightarrow{\partial_d}\widetilde{C}_{d-1}(L;\mathbb{Z})\xrightarrow{\partial_{d-1}}\cdots\xrightarrow{\partial_1}\widetilde{C}_0(L;\mathbb{Z})\xrightarrow{\partial_0}\widetilde{C}_{-1}(L;\mathbb{Z})=\mathbb{Z}\longrightarrow 0,$$
   记 $f_q=\operatorname{rank}(\widetilde{C}_q(L;\mathbb{Z}))$（$f_{-1}=1$，对 $q\ge 0$，$f_q$ 等于 $K$ 中含 $v$ 的 $(q+1)$-单形个数），$r_q=\operatorname{rank}(\partial_q)$（约定 $r_{-1}=r_{d+1}=0$）。则在 S4 前提下，以下三者等价：
   - (i) $X=|K|$ 可缩；
   - (ii) $L=\operatorname{lk}_K(v)$ 整系数无环，即 $\widetilde{H}_q^{\mathrm{simp}}(L;\mathbb{Z})=0$ 对所有 $0\le q\le d$ 成立；
   - (iii) （纯有限整矩阵算法判据）对所有 $q=-1,0,\dots,d$ 满足 $r_q+r_{q+1}=f_q$，且对所有 $q=0,1,\dots,d$，整矩阵 $\partial_q$ 的 Smith 标准形中所有非零不变因子均等于 $1$。

---

### 证明

#### 一、同伦类型刻画的必要性证明（$X\simeq \Sigma|\operatorname{lk}_K(v)|$ 且 $\operatorname{lk}_K(v)\neq\emptyset$）
设 $(K,v,B)$ 满足 S4 的全部条件。记 $D:=|K\setminus v|$，$L:=\operatorname{lk}_K(v)$。

1. **$D$ 非空可缩**：由 S3 引理 3.1，$D=|K\setminus v|$ 是 $O=X\setminus\{v\}$ 的强形变收缩核。因 $O$ 非空可缩，故 $D$ 非空可缩。
2. **$L=\operatorname{lk}_K(v)\neq\emptyset$**：反设 $\operatorname{lk}_B(v)=\emptyset$，即 $B$ 中不含以 $v$ 为真子集的单形。则 $B=(B\setminus v)\sqcup\{\{v\}\}$，故 $C=|B|=|B\setminus v|\sqcup\{v\}$，$O\cap C=|B|\setminus\{v\}=|B\setminus v|$。此时 $\{v\}$ 与 $O\cap C$ 是 $C$ 中互不相交的开闭子集。若包含映射 $\iota\colon O\cap C\hookrightarrow C$ 是同伦等价，则存在 $g\colon C\to O\cap C$（注意若 $O\cap C=\emptyset$ 而 $v\in C$ 则连映射 $g$ 都不存在）及同伦 $H\colon C\times I\to C$ 满足 $H(x,0)=\iota(g(x))$、$H(x,1)=x$；于是 $t\mapsto H(v,t)$ 是 $C$ 中从 $\iota(g(v))\in O\cap C$ 到 $v$ 的连续路径，与 $\{v\}$、$O\cap C$ 为 $C$ 的不交开集分割矛盾！故必有 $\operatorname{lk}_B(v)\neq\emptyset$。由 $B\subseteq K$ 知 $\operatorname{lk}_B(v)\subseteq\operatorname{lk}_K(v)$，因此 $L=\operatorname{lk}_K(v)$ 是**非空**有限抽象单纯复形。
3. **$X\simeq X/D$**：$X=|K|$ 是有限单纯复形（从而有限 CW 复形），$D=|K\setminus v|$ 是非空可缩子复形。由 **S1**（适用条件已逐一核验），商映射 $q\colon X\to X/D$ 是同伦等价。
4. **$X/D\cong \Sigma|L|$**：在 $\mathbb{R}^{V(K)}$ 的标准嵌入下定义 $\varphi\colon |L|\times I\to X/D$ 为
   $$\varphi(y,t):=q\big(t e_v+(1-t)y\big).$$
   - **良定义与连续**：若 $y\in|L|$ 的承载单形为 $\tau\in L$，则 $\tau\cup\{v\}\in K$，故 $t e_v+(1-t)y\in|\tau\cup\{v\}|\subseteq X$，显然连续。
   - **下降至 $\Sigma|L|$**：因 $|L|\subseteq D$，对一切 $y\in|L|$ 有 $\varphi(y,0)=q(y)=q(D)$ 及 $\varphi(y,1)=q(e_v)$，故 $\varphi$ 诱导连续映射 $\bar{\varphi}\colon \Sigma|L|\to X/D$。
   - **满射**：任取 $q(x)\in X/D$。因 $L\neq\emptyset$，可取 $y_0\in|L|$。若 $x\in D$，则 $q(x)=q(D)=\bar{\varphi}([y_0,0])$；若 $x=e_v$，则 $q(x)=\bar{\varphi}([y_0,1])$；若 $x\in X\setminus(D\cup\{e_v\})$，则 $0<\lambda_v(x)<1$，其承载单形 $\sigma$ 含 $v$ 且 $\sigma\neq\{v\}$，故 $\tau:=\sigma\setminus\{v\}\in L$，$y:=\frac{x-\lambda_v(x)e_v}{1-\lambda_v(x)}\in|\tau|\subseteq|L|$ 满足 $x=\lambda_v(x)e_v+(1-\lambda_v(x))y$，从而 $q(x)=\bar{\varphi}([y,\lambda_v(x)])$。
   - **单射**：因 $e_v\notin D$，两个极点像 $q(D)$ 与 $q(e_v)$ 互异，且均异于 $q(X\setminus(D\cup\{e_v\}))$ 中的点；在 $|L|\times(0,1)$ 上，$x=t e_v+(1-t)y$ 满足 $\lambda_v(x)=t\in(0,1)$ 故 $x\notin D$，而 $q$ 在 $X\setminus D$ 上单射，且由 $x$ 可唯一还原 $t=\lambda_v(x)$ 与 $y=\frac{x-t e_v}{1-t}$。
   - **同胚**：$|L|\times I$ 紧，故 $\Sigma|L|$ 紧；$X$ 紧 Hausdorff（从而正规）且 $D$ 闭，故 $X/D$ 为 Hausdorff 空间（$X\setminus D$ 内两点在开集 $X\setminus D$ 中分离；$x\in X\setminus D$ 与 $D$ 由正规性有不交开邻域 $U\ni x$、$V\supseteq D$，它们关于 $q$ 饱和并映为 $X/D$ 中的不交开邻域）。紧空间到 Hausdorff 空间的连续双射必为同胚，故 $\bar{\varphi}\colon \Sigma|L|\xrightarrow{\cong} X/D$。

综合第 3、4 步得 $X\simeq X/D\cong \Sigma|L|$，其中 $L=\operatorname{lk}_K(v)$ 为非空有限抽象单纯复形。*(注：亦可由 $X=D\cup_{|L|} C|L|$ 结合 S2 得 $X\simeq D\vee\Sigma|L|\simeq \Sigma|L|$。)*

---

#### 二、实现构造的充分性证明
任给非空有限抽象单纯复形 $L$，取互异新顶点 $u,v\notin V(L)$ 及任一顶点 $w\in V(L)$，令
$$K=\{u,v\}*L,\qquad B=\{\{v\},\{w\},\{v,w\}\}.$$
与 S3 第 1–4 步的验证完全逐字相同：
- $K$ 是有限抽象单纯复形，$v\in V(K)$，$B\subseteq K$ 是含 $v$ 子复形；
- $O=|K|\setminus\{v\}$ 以 $|K\setminus v|=|u*L|$ 为强形变收缩核，故 $O$ 非空可缩；
- $O\cap C=[e_w,e_v)\hookrightarrow [e_w,e_v]=C$ 是同伦等价；
- $X=|K|\cong \Sigma|L|$。

这就为刻画中的全部同伦类型给出了满足原条件的实现构造。

---

#### 三、可缩判据的证明

首先说明 $L=\operatorname{lk}_K(v)$ 的增广整系数单纯链复形 $\widetilde{C}_*(L;\mathbb{Z})$ **仅依赖于 $K$ 中含 $v$ 的单形及其面之间的有限关联数据**：
- 含 $v$ 的单形集为 $\operatorname{St}_K(v)=\{\sigma\in K:v\in\sigma\}$；每个非 $\{v\}$ 的含 $v$ 单形 $\sigma$ 删去 $v$ 所得的余维 $1$ 面 $\tau=\sigma\setminus\{v\}$ 恰构成 $L=\operatorname{lk}_K(v)$ 的全部单形，而 $L$ 中单形间的面包含关系即这些面之间的有限关联关系。
- 任选 $V(L)$ 的一个全序后，边界算子 $\partial_q\colon \widetilde{C}_q(L;\mathbb{Z})\to\widetilde{C}_{q-1}(L;\mathbb{Z})$（$q\ge 1$ 时为标准交错面和，$q=0$ 时为增广映射 $\partial_0([w])=1\in\mathbb{Z}$）是完全由该有限关联数据确定的整矩阵，且当 $q>d:=\dim L$ 时 $\widetilde{C}_q(L;\mathbb{Z})=0$。

##### 证明 (i) $\Longleftrightarrow$ (ii)
因 $L$ 是有限抽象单纯复形，其约化单纯同调与几何实现的约化奇异同调自然同构：$\widetilde{H}_q^{\mathrm{simp}}(L;\mathbb{Z})\cong \widetilde{H}_q(|L|;\mathbb{Z})$（$\forall q\ge 0$），且对 $q>d$ 自动为零。已知 $L\neq\emptyset$ 且 $X\simeq\Sigma|L|$。

- **必要性 (i) $\Rightarrow$ (ii)**：若 $X$ 可缩，则 $\Sigma|L|\simeq X$ 可缩。由约化奇异同调的同伦不变性，$\widetilde{H}_n(\Sigma|L|;\mathbb{Z})=0$（$\forall n\ge 0$）。因 $|L|\neq\emptyset$，由 S3 引理 3.2（悬挂同调同构），对一切 $q\ge 0$ 有
  $$\widetilde{H}_q^{\mathrm{simp}}(L;\mathbb{Z})\cong \widetilde{H}_q(|L|;\mathbb{Z})\cong \widetilde{H}_{q+1}(\Sigma|L|;\mathbb{Z})=0.$$

- **充分性 (ii) $\Rightarrow$ (i)**：假设 $\widetilde{H}_q^{\mathrm{simp}}(L;\mathbb{Z})=0$ 对所有 $0\le q\le d$ 成立，从而 $\widetilde{H}_q(|L|;\mathbb{Z})=0$ 对所有 $q\ge 0$ 成立。
  1. **$|L|$ 路径连通**：因 $H_0(|L|;\mathbb{Z})\cong\mathbb{Z}^{\pi_0(|L|)}$ 且 $|L|\neq\emptyset$，$\widetilde{H}_0(|L|;\mathbb{Z})=0$ 推出 $|\pi_0(|L|)|=1$，即 $|L|$ 路径连通。
  2. **$\Sigma|L|$ 单连通（Seifert–van Kampen 定理）**：取开覆盖 $\Sigma|L|=U\cup V$，其中 $U=\Sigma|L|\setminus\{s_-\}$、$V=\Sigma|L|\setminus\{s_+\}$。检验适用条件：$U,V$ 均开且覆盖 $\Sigma|L|$；$U,V$ 均可缩，故路径连通且 $\pi_1(U)=1,\pi_1(V)=1$；$U\cap V\cong |L|\times(0,1)$ 非空且因 $|L|$ 路径连通而**路径连通**。任取基点 $x_0\in U\cap V$，由 Seifert–van Kampen 定理得
     $$\pi_1(\Sigma|L|,x_0)\cong \pi_1(U,x_0)*_{\pi_1(U\cap V,x_0)}\pi_1(V,x_0)=1.$$
     故 $\Sigma|L|$ 路径连通且单连通。
  3. **$\Sigma|L|$ 全部同伦群平凡（Hurewicz 定理）**：因 $|L|\neq\emptyset$，由 S3 引理 3.2 得 $\widetilde{H}_k(\Sigma|L|;\mathbb{Z})=0$ 对一切 $k\ge 0$ 成立。对 $n\ge 2$ 归纳证 $\pi_n(\Sigma|L|,x_0)=0$：若对一切 $1\le i<n$ 已有 $\pi_i(\Sigma|L|,x_0)=0$（基步 $n=2$ 即第 2 步的 $\pi_1=0$），则 $\Sigma|L|$ 是 $(n-1)$-连通空间（$n\ge 2$），满足 **Hurewicz 定理** 适用条件，故 Hurewicz 同态 $\pi_n(\Sigma|L|,x_0)\xrightarrow{\cong} H_n(\Sigma|L|;\mathbb{Z})=\widetilde{H}_n(\Sigma|L|;\mathbb{Z})=0$ 为同构，即 $\pi_n(\Sigma|L|,x_0)=0$。归纳完毕。
  4. **$X$ 可缩（Whitehead 定理）**：因 $X\simeq\Sigma|L|$，故 $X$ 路径连通且对任意 $x_1\in X$ 及所有 $n\ge 1$ 有 $\pi_n(X,x_1)=0$。考虑常值映射 $c\colon X\to\{*\}$。检验 **Whitehead 定理** 适用条件：$X=|K|$ 与单点空间 $\{*\}$ 均为 CW 复形（有限单纯复形），且 $c$ 在 $\pi_0$ 上诱导双射、在所有 $n\ge 1$ 上诱导群同构 $c_*\colon \pi_n(X,x_1)\xrightarrow{\cong}\pi_n(\{*\},*)=0$。由 Whitehead 定理，$c\colon X\to\{*\}$ 是同伦等价，即 $X$ 可缩。

##### 证明 (ii) $\Longleftrightarrow$ (iii)
对每个 $q\in\{-1,0,\dots,d\}$，因 $L\neq\emptyset$，增广映射 $\partial_0=(1,\dots,1)\colon \mathbb{Z}^{f_0}\to\mathbb{Z}$ 满射（$r_0=1=f_{-1}$，唯一非零不变因子为 $1$），故 $\widetilde{H}_{-1}(L;\mathbb{Z})=0$ 自动成立。对任意 $q\in\{-1,0,\dots,d\}$，记 $C_q=\widetilde{C}_q(L;\mathbb{Z})\cong\mathbb{Z}^{f_q}$，有短正合列
$$0\longrightarrow \underbrace{\ker(\partial_q)/\operatorname{im}(\partial_{q+1})}_{\widetilde{H}_q(L;\mathbb{Z})} \longrightarrow C_q/\operatorname{im}(\partial_{q+1}) \xrightarrow{\;\bar{\partial}_q\;} \operatorname{im}(\partial_q) \longrightarrow 0$$
（约定 $\partial_{d+1}=0,\partial_{-1}=0$）。因 $\operatorname{im}(\partial_q)\subseteq C_{q-1}$ 是有限秩自由阿贝尔群的子群，故 $\operatorname{im}(\partial_q)\cong\mathbb{Z}^{r_q}$ 自由，该短正合列分裂：
$$C_q/\operatorname{im}(\partial_{q+1})\cong \widetilde{H}_q(L;\mathbb{Z})\oplus \mathbb{Z}^{r_q}.$$
另一方面，设整矩阵 $\partial_{q+1}\colon\mathbb{Z}^{f_{q+1}}\to\mathbb{Z}^{f_q}$ 的 Smith 标准形为 $\operatorname{diag}(s_1,\dots,s_{r_{q+1}},0,\dots,0)$（其中 $s_i\in\mathbb{Z}_{\ge 1},\,s_1\mid\cdots\mid s_{r_{q+1}}$），则
$$C_q/\operatorname{im}(\partial_{q+1})\cong \mathbb{Z}^{f_q-r_{q+1}}\oplus \bigoplus_{i=1}^{r_{q+1}}\mathbb{Z}/s_i\mathbb{Z}.$$
比较两式的自由秩与挠子群（有限生成阿贝尔群基本定理）：
$$\operatorname{rank}\big(\widetilde{H}_q(L;\mathbb{Z})\big)=f_q-r_q-r_{q+1},\qquad \operatorname{Tors}\big(\widetilde{H}_q(L;\mathbb{Z})\big)\cong \bigoplus_{i=1}^{r_{q+1}}\mathbb{Z}/s_i\mathbb{Z}.$$
因此 $\widetilde{H}_q(L;\mathbb{Z})=0$ 对全部 $q\in\{-1,0,\dots,d\}$ 成立，当且仅当对全部 $q\in\{-1,0,\dots,d\}$ 有 $r_q+r_{q+1}=f_q$ 且对全部 $q\in\{-1,0,\dots,d-1\}$（即 $\partial_0,\partial_1,\dots,\partial_d$，因为 $\partial_{d+1}=0$ 无非零不变因子）其 Smith 标准形的所有非零不变因子均等于 $1$。此条件仅经有限步整矩阵初等行列变换即可判定。$\square$

---

## S5 不提供子复形 $B$

### 判定结论
**不必。** 去掉子复形 $B$ 及其同伦条件后，$|K|$ 不必同伦等价于非空有限复形的悬挂；**新增的可能同伦类型有且仅有一种，即两点离散空间 $S^0$ 的同伦类型**。

### 证明与分类
设 $K$ 是有限抽象单纯复形，$v\in V(K)$，仅假设 $O=|K|\setminus\{v\}$ 非空可缩。由 S3 引理 3.1，$D=|K\setminus v|$ 仍是 $O$ 的强形变收缩核，故 $D$ 非空可缩。按 $L:=\operatorname{lk}_K(v)$ 是否非空分为仅有的两种情形：

1. **情形 1：$L=\operatorname{lk}_K(v)\neq\emptyset$**。
   注意 S4 第一部分中证明 $X\simeq X/D\cong \Sigma|L|$ 时，对 $B$ 的唯一使用就是导出 $L\neq\emptyset$。因此在此情形下完全沿用 S4 的证明（应用 S1 于有限 CW 对 $(|K|,D)$），仍得 $|K|\simeq\Sigma|L|$，是非空有限单纯复形（亦是有限 CW 复形）的悬挂。

2. **情形 2：$L=\operatorname{lk}_K(v)=\emptyset$**（即 $v$ 是 $K$ 的孤立顶点）。
   此时 $K=(K\setminus v)\sqcup\{\{v\}\}$，故 $|K|=D\sqcup\{v\}$（其中 $D$ 与 $\{v\}$ 均为开闭子集）。因 $D$ 非空可缩，取 $d_0\in D$ 及收缩同伦 $H\colon D\times I\to D$（$H(x,0)=x,\,H(x,1)=d_0$）。记 $S^0=\{0,1\}$，定义连续映射
   $$f\colon |K|\to S^0,\quad f(D)=\{0\},\;f(v)=1;\qquad g\colon S^0\to |K|,\quad g(0)=d_0,\;g(1)=v.$$
   则 $f\circ g=\mathrm{id}_{S^0}$，且在 $|K|\times I=(D\times I)\sqcup(\{v\}\times I)$ 上令 $F(x,t)=H(x,t)$（$x\in D$）、$F(v,t)=v$ 给出 $\mathrm{id}_{|K|}\simeq g\circ f$。故 $|K|\simeq S^0$。

3. **确认 $S^0$ 可实现且确为新增类型**：
   - **实现**：取 $K=\{\{u\},\{v\}\}$（两孤立顶点）。显然 $K$ 有限，$|K|\setminus\{v\}=\{u\}$ 非空可缩，且 $|K|\cong S^0$。
   - **并非任何非空空间的悬挂**：对任意非空拓扑空间 $Y$（特别是任意非空有限单纯复形或有限 CW 复形），取 $y_0\in Y$，则 $\Sigma Y$ 中任一点 $[y,t]$ 均可经连续路径 $s\mapsto [y,(1-s)t]$ 连至南极 $s_-=[y_0,0]$，故 $\Sigma Y$ **路径连通**（$|\pi_0(\Sigma Y)|=1$）。然而 $|\pi_0(S^0)|=2$。因路径连通分支个数 $|\pi_0(-)|$ 是同伦不变量，故对任意非空空间 $Y$ 均有 $S^0\not\simeq\Sigma Y$。

综上，不提供 $B$ 时，新增的可能同伦类型恰为 $S^0$ 这一种。$\square$

---

## S6 悬挂信息的逆向恢复

### 判定结论
**否。** 对非空有限抽象单纯复形 $L_1,L_2$，$\Sigma|L_1|\simeq\Sigma|L_2|$ **不必**推出 $|L_1|\simeq|L_2|$。

### 反例构造
1. 取 $L_1:=\{\{p\}\}$（单个顶点），显然 $L_1$ 是非空有限抽象单纯复形，$|L_1|=\{p\}$ 为单点空间。
2. 考虑带有平衡有限群展示的非平凡完全群
   $$G:=\langle x,y\mid r_1=1,\;r_2=1\rangle,\qquad r_1=x^2y^{-3},\quad r_2=x^2(yx^{-1})^5,$$
   及其对应的二维展示 CW 复形 $P=(S^1_x\vee S^1_y)\cup_{r_1}D^2_1\cup_{r_2}D^2_2$。我们显式构造有限抽象单纯复形 $L_2$ 使 $|L_2|\cong P$：
   - **1-骨架三角剖分 $W$**：取 5 个顶点 $p_0,x_1,x_2,y_1,y_2$ 和 6 条边 $\{p_0,x_1\},\{x_1,x_2\},\{x_2,p_0\}$（定向 $p_0\to x_1\to x_2\to p_0$ 代表环路 $x$）与 $\{p_0,y_1\},\{y_1,y_2\},\{y_2,p_0\}$（定向 $p_0\to y_1\to y_2\to p_0$ 代表环路 $y$）。显然 $|W|\cong S^1_x\vee S^1_y$。
   - **将关系词写成 $W$ 中的闭边路**：
     - $r_1=x^2y^{-3}$ 对应长度为 $m_1=15$ 的闭边路 $(a_0,a_1,\dots,a_{15})$：
       $$(p_0,x_1,x_2,p_0,x_1,x_2,p_0,y_2,y_1,p_0,y_2,y_1,p_0,y_2,y_1,p_0),$$
       满足 $a_{15}=a_0=p_0$ 且每对相邻顶点 $\{a_i,a_{i+1}\}\in W$（故 $a_i\neq a_{i+1}$）。
     - $r_2=x^2(yx^{-1})^5$（先走两遍 $x$，再重复五遍 $p_0\to y_1\to y_2\to p_0\to x_2\to x_1\to p_0$）对应长度为 $m_2=36$ 的闭边路 $(b_0,b_1,\dots,b_{36})$，满足 $b_{36}=b_0=p_0$ 且 $\{b_j,b_{j+1}\}\in W$（故 $b_j\neq b_{j+1}$）。
   - **带领圈的圆盘粘接三角剖分 $L_2$**：引入两批与 $V(W)$ 及彼此均互不相交的新顶点
     $$U_1=\{c_1,u_0,\dots,u_{14}\},\qquad U_2=\{c_2,v_0,\dots,v_{35}\}$$
     （$u_i$ 下标模 $15$，$v_j$ 下标模 $36$）。定义 $L_2$ 为由以下单形及其全部非空面生成的有限抽象单纯复形（共 $5+16+37=58$ 个顶点、$3(15+36)=153$ 个 $2$-单形）：
     - $W$ 的全部边；
     - 对 $i=0,\dots,14$：$2$-单形 $\{u_i,a_i,a_{i+1}\}$、$\{u_i,u_{i+1},a_{i+1}\}$、$\{c_1,u_i,u_{i+1}\}$；
     - 对 $j=0,\dots,35$：$2$-单形 $\{v_j,b_j,b_{j+1}\}$、$\{v_j,v_{j+1},b_{j+1}\}$、$\{c_2,v_j,v_{j+1}\}$。
     （因 $a_i\neq a_{i+1}$、$b_j\neq b_{j+1}$、$m_1,m_2\ge 3$ 且 $V(W),U_1,U_2$ 两两不交，以上所有三元组均含三个互异顶点。）

### 证明满足全部条件且构成反例

#### 步骤 1：证明 $|L_2|\cong P$
对任意 $m\ge 3$，构造抽象单纯复形 $D_m$，顶点集为 $2m+1$ 个互异顶点 $\{c,u_0,\dots,u_{m-1},w_0,\dots,w_{m-1}\}$，$2$-单形为 $\{u_i,w_i,w_{i+1}\}$、$\{u_i,u_{i+1},w_{i+1}\}$、$\{c,u_i,u_{i+1}\}$（$0\le i<m$，下标模 $m$）。在 $\mathbb{R}^2$ 中取 $c=(0,0)$、$u_i=(\cos\frac{2\pi i}{m},\sin\frac{2\pi i}{m})$、$w_i=2u_i$。对每个扇区（以 $u_i,u_{i+1}$ 为基的非负线性组合 $su_i+tu_{i+1}$，$s,t\ge 0$）：
- $\triangle(c,u_i,u_{i+1})$ 为 $\{s+t\le 1\}$；
- $\triangle(u_i,u_{i+1},w_{i+1})$ 为 $\{1\le s+t,\,2s+t\le 2\}$；
- $\triangle(u_i,w_i,w_{i+1})$ 为 $\{s+t\le 2,\,2s+t\ge 2\}$。

三者无重叠地铺满 $\{s+t\le 2\}$，并遍及 $i=0,\dots,m-1$ 拼成半径为 $2$ 的凸正 $m$ 边形，故 $|D_m|\cong D^2$ 且边界 $|\partial D_m|$ 恰为外圈 $m$-边形 $(w_0,w_1,\dots,w_{m-1})$。

取 $D^{(1)}:=D_{15}$（外圈顶点 $w_i$，内点集 $U_1$）与 $D^{(2)}:=D_{36}$（外圈顶点 $z_j$，内点集 $U_2$）。单纯映射 $\varphi_1\colon D^{(1)}\to L_2$（$w_i\mapsto a_i,\,u_i\mapsto u_i,\,c_1\mapsto c_1$）与 $\varphi_2\colon D^{(2)}\to L_2$（$z_j\mapsto b_j,\,v_j\mapsto v_j,\,c_2\mapsto c_2$）在每个单形的顶点上单射，合并包含映射 $|W|\hookrightarrow|L_2|$ 得连续满射
$$\Phi\colon |W|\sqcup|D^{(1)}|\sqcup|D^{(2)}|\longrightarrow |L_2|.$$
检验 $\Phi$ 的纤维：
- $|W|$、$\operatorname{int}(|D^{(1)}|)$、$\operatorname{int}(|D^{(2)}|)$ 中点在 $\Phi$ 下的像分别满足：在 $U_1\cup U_2$ 上重心坐标全为零、在 $U_1$ 上有正坐标且在 $U_2$ 上为零、在 $U_2$ 上有正坐标且在 $U_1$ 上为零，故三者的像两两不交；
- $\Phi|_{|W|}=\mathrm{id}_{|W|}$ 单射；
- $\Phi|_{\operatorname{int}(|D^{(1)}|)}$ 单射：若 $p,p'\in\operatorname{int}(|D^{(1)}|)$ 满足 $\Phi(p)=\Phi(p')$，设其在 $D^{(1)}$ 中的承载单形为 $\sigma,\sigma'$。比较 $U_1$ 上正坐标得 $S:=\sigma\cap U_1=\sigma'\cap U_1\neq\emptyset$。分类检查：
  - 若 $c_1\in S$，则 $D^{(1)}$ 中含 $c_1$ 的单形均含于 $U_1$，故 $\sigma=S=\sigma'$；
  - 若 $S=\{u_i,u_{i+1}\}$，仅有 $\{u_i,u_{i+1}\}$ 与 $\{u_i,u_{i+1},w_{i+1}\}$ 两种单形，其像顶点数分别为 $2$ 与 $3$，故必 $\sigma=\sigma'$；
  - 若 $S=\{u_i\}$，$D^{(1)}$ 中与 $U_1$ 交为 $\{u_i\}$ 的单形仅有 $\{u_i\}$、$\{u_i,w_i\}$、$\{u_i,w_{i+1}\}$、$\{u_i,w_i,w_{i+1}\}$ 四种，因 $a_i\neq a_{i+1}$，它们在 $\varphi_1$ 下的像 $\{u_i\}$、$\{u_i,a_i\}$、$\{u_i,a_{i+1}\}$、$\{u_i,a_i,a_{i+1}\}$ 两两不同，故必 $\sigma=\sigma'$。
  再因 $\varphi_1|_\sigma$ 单射，得 $p=p'$。同理 $\Phi|_{\operatorname{int}(|D^{(2)}|)}$ 单射；
- 在边界 $|\partial D^{(1)}|$ 与 $|\partial D^{(2)}|$ 上，$\Phi$ 分别沿 $r_1$ 与 $r_2$ 映入 $|W|$。

因此 $\Phi$ 所诱导的等价关系与 $P=|W|\cup_{r_1}|D^{(1)}|\cup_{r_2}|D^{(2)}|$ 的定义等价关系完全一致，从而诱导连续双射 $\bar{\Phi}\colon P\to|L_2|$。因 $P$ 紧（紧空间的商）、$|L_2|$ Hausdorff（有限单纯复形），故 $\bar{\Phi}$ 是**同胚**，即 $|L_2|\cong P$。

#### 步骤 2：证明 $\Sigma|L_1|\simeq\Sigma|L_2|$
1. 对 $L_1=\{\{p\}\}$，$|L_1|=\{p\}$，故 $\Sigma|L_1|\cong I$ 可缩。
2. 计算 $P$ 的整系数奇异同调：因 $P$ 是有限 CW 复形，其胞腔同调与奇异同调同构。$P$ 的胞腔链复形为
   $$0\longrightarrow \mathbb{Z}e^2_1\oplus\mathbb{Z}e^2_2 \xrightarrow{\;\partial_2\;} \mathbb{Z}e^1_x\oplus\mathbb{Z}e^1_y \xrightarrow{\;\partial_1=0\;} \mathbb{Z}e^0 \longrightarrow 0.$$
   按胞腔边界公式，将 $S^1_x\vee S^1_y$ 分别坍缩掉 $S^1_y$ 或 $S^1_x$，粘接映射的度数即为关系词中 $x,y$ 的指数和：
   - $r_1=x^2y^{-3}$：$x$-指数和为 $2$，$y$-指数和为 $-3$；
   - $r_2=x^2(yx^{-1})^5$：$x$-指数和为 $2-5=-3$，$y$-指数和为 $5$。
   故 $\partial_2$ 在基 $(e^2_1,e^2_2)$ 与 $(e^1_x,e^1_y)$ 下的矩阵为
   $$M=\begin{pmatrix} 2 & -3 \\ -3 & 5 \end{pmatrix},\qquad \det M=2\cdot 5-(-3)(-3)=1.$$
   因此 $\partial_2$ 是 $\mathbb{Z}$-模同构（逆矩阵为 $\begin{pmatrix}5&3\\3&2\end{pmatrix}$），由此直接得
   $$H_2(P;\mathbb{Z})=\ker\partial_2=0,\qquad H_1(P;\mathbb{Z})=\operatorname{coker}\partial_2=0,\qquad \widetilde{H}_0(P;\mathbb{Z})=0,$$
   且对 $q\ge 3$ 无 $q$-胞腔故 $H_q(P;\mathbb{Z})=0$。由 $|L_2|\cong P$ 知 $\widetilde{H}_q(|L_2|;\mathbb{Z})=0$ 对一切 $q\ge 0$ 成立。
3. 现对非空有限抽象单纯复形 $L_2$ 应用 **S4 的充分性证明**（具体地：可取实现 $K=\{u,v\}*L_2$ 与 $B=\{\{v\},\{p_0\},\{v,p_0\}\}$，满足 S4 全部前提且 $|K|\cong\Sigma|L_2|$；因 $\widetilde{H}_*(L_2;\mathbb{Z})=0$，由 S4 的可缩判据即知 $\Sigma|L_2|$ 可缩！）。
4. 因 $\Sigma|L_1|$ 与 $\Sigma|L_2|$ 均可缩，故 $\Sigma|L_1|\simeq *\simeq \Sigma|L_2|$。

#### 步骤 3：证明 $|L_1|\not\simeq|L_2|$
由二维 CW 复形粘接 $2$-胞腔的基本群定理（Seifert–van Kampen 定理的标准推论，适用条件：$S^1_x\vee S^1_y$ 路径连通且各 $2$-胞腔沿闭路粘接），
$$\pi_1(|L_2|,p_0)\cong \pi_1(P,p_0)\cong G=\langle x,y\mid x^2y^{-3}=1,\;x^2(yx^{-1})^5=1\rangle.$$
构造群同态 $\rho\colon G\to A_5$（取置换的左复合 $(\alpha\beta)(k)=\alpha(\beta(k))$）：令
$$\sigma=(1\,2)(3\,4)\in A_5,\qquad \tau=(1\,3\,5)\in A_5.$$
直接计算：
- $\sigma^2=\mathrm{id}$，$\sigma^{-1}=\sigma$；$\tau^3=\mathrm{id}$，$\tau^{-3}=\mathrm{id}$；
- $\tau\sigma^{-1}=\tau\sigma$ 满足：
  $$1\mapsto \tau(2)=2,\quad 2\mapsto\tau(1)=3,\quad 3\mapsto\tau(4)=4,\quad 4\mapsto\tau(3)=5,\quad 5\mapsto\tau(5)=1,$$
  即 $\tau\sigma^{-1}=(1\,2\,3\,4\,5)$，故 $(\tau\sigma^{-1})^5=\mathrm{id}$。

于是 $\sigma^2\tau^{-3}=\mathrm{id}$ 且 $\sigma^2(\tau\sigma^{-1})^5=\mathrm{id}$，从而 $x\mapsto\sigma,\,y\mapsto\tau$ 良定义群同态 $\rho\colon G\to A_5$。因 $\rho(x)=\sigma\neq\mathrm{id}$，故 $\pi_1(|L_2|,p_0)\cong G\neq\{1\}$。另一方面，$\pi_1(|L_1|,p)=\{1\}$。因路径连通空间的基本群同构类是同伦不变量，故 $|L_1|\not\simeq|L_2|$。$\square$