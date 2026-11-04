## #h-86ff0bbbdf478a45 经验网络拟合

当代理算子带有有限算子网络表示时，经验数据可以沿代理路径、前缀发生和节点发生重新组织。残差、共同锚点距离与保证域由此获得路径局部形式。有限采样本身不指定目标的网络表示；目标路径、形态标签与节点分解只有在目标端网络证书被额外给出时才成为可用对象。

### #h-55c4fe8427039cfc 代理路径上的采样分解

本节固定扩展规范空间 $(\mathcal X,\mathcal G,\bot)$ 与有限指标集 $I$。设目标算子 $\phi^\natural\in\mathcal X_{\mathrm{op}}$、代理算子 $\phi\in\mathcal X_{\mathrm{op}}$，并设

$$
U\subseteq\mathrm{dom}(\phi)\cap V^*,
$$

其中 $(V^*,\mathbf L^*)$ 是目标 Lip 包络证书（@h-9655cbb9401e5c90）。设 $\mathcal N$ 是输入域为 $U$ 的有限算子网络，并且是 $\phi$ 在 $U$ 上的网络表示：

$$
\phi_\mathcal N\equiv_U\phi .
$$

记代理网络的路径集为 $\mathcal P=\mathcal P(\mathcal N)$，路径域分划为

$$
U=\bigsqcup_{q\in\mathcal P}U_q,
$$

路径链为 $c_q$（@h-374f884cd4d69e88、@h-56edb9917107efcd）。采样结构沿用 @h-6f9e054ce01ccfef：

$$
\mathcal S=\{S_j\}_{j\in I},
\qquad
S_j\subseteq S\cap U\cap\mathrm{dom}(\phi^\natural),
\qquad
I_{\mathrm{res}}=\{j\in I:S_j\neq\emptyset\}.
$$

**定义（路径采样集）**：对路径 $q\in\mathcal P$ 与分量 $j\in I_{\mathrm{res}}$，定义

$$
S_{q,j}=S_j\cap U_q.
$$

若 $S_{q,j}\neq\emptyset$，称 $j$ 在路径 $q$ 上可评估，并定义

$$
I_{\mathrm{res}}(q)=\{j\in I_{\mathrm{res}}:S_{q,j}\neq\emptyset\}.
$$

固定与 @h-6f9e054ce01ccfef 相同的采样分辨修正 $\delta_{o,j}$，路径级经验残差上界定义为

$$
\hat\varepsilon_{q,j}
=
\sup_{x_s\in S_{q,j}}
d_j(c_q(x_s),\phi^\natural(x_s))
+\delta_{o,j}
\qquad(j\in I_{\mathrm{res}}(q)).
$$

由于 $x_s\in U_q$ 时 $c_q(x_s)=\phi(x_s)$，该残差由全局残差所用的点态偏差函数限制到 $S_{q,j}$ 后重新取上确界得到。

**命题 #h-ed8808b4cfd52216（路径采样分解）**：对每个 $j\in I_{\mathrm{res}}$，

$$
S_j=\bigsqcup_{q\in\mathcal P}S_{q,j}.
$$

进一步，若 $j\in I_{\mathrm{res}}(q)$，则

$$
\hat\varepsilon_{q,j}\leq\hat\varepsilon_j .
$$

若 $j\notin I_{\mathrm{res}}(q)$，则路径 $q$ 上没有第 $j$ 分量的路径级经验残差，也不能用 $S_{q,j}$ 构造第 $j$ 分量的路径级共同锚点证书。

**证明**：路径域族 $\{U_q\}_{q\in\mathcal P}$ 由 @h-56edb9917107efcd 构成 $U$ 的不交分划。由于 $S_j\subseteq U$，与该分划取交得到第一式。若 $S_{q,j}\neq\emptyset$，则 $S_{q,j}\subseteq S_j$，且 $c_q=\phi$ 在 $U_q$ 上成立，因此

$$
\sup_{x_s\in S_{q,j}}d_j(c_q(x_s),\phi^\natural(x_s))
\leq
\sup_{x_s\in S_j}d_j(\phi(x_s),\phi^\natural(x_s)).
$$

两侧加同一个 $\delta_{o,j}$ 得到 $\hat\varepsilon_{q,j}\leq\hat\varepsilon_j$。最后一句只是 $S_{q,j}=\emptyset$ 时 @h-6f9e054ce01ccfef 的非空锚点条件不成立。$\square$

> **注（路径采样缺失）**：当 $S_{q,j}=\emptyset$ 时，共同锚点距离
> $D_{\mathbf A_q,j}(x;S_{q,j})$ 不在本章定义范围内，因而相应路径级证书停止。真实偏差不出现在这一空集条件中；若改用全局 $S_j$，仍可在满足 @h-f16da76e4331b725 全部前提时使用全局证书。

### #h-0056e459b9376864 路径局部经验保证域

设 $q\in\mathcal P$，$j\in I_{\mathrm{res}}(q)$。取路径链的受限 Lip 证书

$$
\mathbf L_q\in\mathscr L(c_q)\big|_{U_q},
$$

并令

$$
\mathbf A_q=\mathbf L_q+\mathbf L^*.
$$

**定义（路径分量经验保证域）**：对有限阈值 $\tau_j\in[0,+\infty)$，定义

$$
U_{q,j}(\tau_j)
=
\{x\in U_q:
D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}\leq\tau_j\}.
$$

对非空 $J_q\subseteq I_{\mathrm{res}}(q)$ 与阈值族 $\boldsymbol\tau=(\tau_j)_{j\in J_q}$，定义

$$
U_{q,J_q}(\boldsymbol\tau)
=
\bigcap_{j\in J_q}U_{q,j}(\tau_j).
$$

**命题 #h-4b5219aa3a3bbdad（路径局部经验上界）**：在上述设定下，对任意 $x\in U_q$，

$$
d_j(\phi(x),\phi^\natural(x))
\leq
D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}.
$$

因此若 $x\in U_{q,j}(\tau_j)$，则

$$
d_j(\phi(x),\phi^\natural(x))\leq\tau_j.
$$

若 $x\in U_{q,J_q}(\boldsymbol\tau)$，则上述结论对所有 $j\in J_q$ 同时成立。

**证明**：固定 $x\in U_q$ 与 $x_s\in S_{q,j}$。由路径分解，$c_q(x)=\phi(x)$ 且 $c_q(x_s)=\phi(x_s)$。三角不等式给出

$$
d_j(\phi(x),\phi^\natural(x))
\leq
d_j(c_q(x),c_q(x_s))
+d_j(c_q(x_s),\phi^\natural(x_s))
+d_j(\phi^\natural(x_s),\phi^\natural(x)).
$$

由 $\mathbf L_q$ 与 $\mathbf L^*$ 的 Lip 证书，

$$
d_j(c_q(x),c_q(x_s))
\leq
\sum_{i\in I}[\mathbf L_q]_{i\to j}d_i(x,x_s),
$$

$$
d_j(\phi^\natural(x_s),\phi^\natural(x))
\leq
\sum_{i\in I}[\mathbf L^*]_{i\to j}d_i(x_s,x).
$$

由伪度量对称性和路径残差定义，

$$
d_j(\phi(x),\phi^\natural(x))
\leq
\sum_{i\in I}[\mathbf A_q]_{i\to j}d_i(x,x_s)+\hat\varepsilon_{q,j}.
$$

该式对所有 $x_s\in S_{q,j}$ 成立，对同一锚点加权和取下确界得到第一式。其余结论由定义直接代入。$\square$

**命题 #h-4091a4a3834bf02c（路径局部正偏差下界证书）**：设 $q\in\mathcal P$、$j\in I_{\mathrm{res}}(q)$、$x\in U_q$、$x_s\in S_{q,j}$，并取 $a\in[0,+\infty)$。

**(i)** 若

$$
\mathbf K_q\in\mathscr K(c_q)\big|_{U_q},
\qquad
\mathbf L^*\in\mathscr L(\phi^\natural)\big|_{V^*},
$$

且

$$
a+\sum_{i\in I}[\mathbf L^*]_{i\to j}d_i(x,x_s)+\hat\varepsilon_{q,j}
<
\sum_{i\in I}[\mathbf K_q]_{i\to j}d_i(x,x_s),
$$

则

$$
d_j(\phi(x),\phi^\natural(x))>a.
$$

**(ii)** 若

$$
\mathbf K^*\in\mathscr K(\phi^\natural)\big|_{V^*},
\qquad
\mathbf L_q\in\mathscr L(c_q)\big|_{U_q},
$$

且

$$
a+\sum_{i\in I}[\mathbf L_q]_{i\to j}d_i(x,x_s)+\hat\varepsilon_{q,j}
<
\sum_{i\in I}[\mathbf K^*]_{i\to j}d_i(x,x_s),
$$

则同样有

$$
d_j(\phi(x),\phi^\natural(x))>a.
$$

**证明**：证明 (i)。反设 $d_j(\phi(x),\phi^\natural(x))\leq a$。由 $x,x_s\in U_q$，路径分解给出 $c_q(x)=\phi(x)$ 与 $c_q(x_s)=\phi(x_s)$。三角不等式给出

$$
d_j(c_q(x),c_q(x_s))
\leq
d_j(\phi(x),\phi^\natural(x))
+d_j(\phi^\natural(x),\phi^\natural(x_s))
+d_j(\phi^\natural(x_s),\phi(x_s)).
$$

右侧不超过

$$
a+\sum_{i\in I}[\mathbf L^*]_{i\to j}d_i(x,x_s)+\hat\varepsilon_{q,j}.
$$

另一方面，$\mathbf K_q$ 的 co-Lip 下界给出

$$
\sum_{i\in I}[\mathbf K_q]_{i\to j}d_i(x,x_s)
\leq
d_j(c_q(x),c_q(x_s)).
$$

这与 (i) 的严格不等式矛盾，故 $d_j(\phi(x),\phi^\natural(x))>a$。

证明 (ii) 时交换代理路径链与目标的角色：用 $\mathbf K^*$ 给目标像距下界，用 $\mathbf L_q$ 给代理路径像距上界，并仍使用 $c_q(x_s)=\phi(x_s)$ 与路径残差上界。$\square$

**推论 #h-93b9c20ea18b4e59（路径保证域的全局拟合含义）**：对任意 $j\in I_{\mathrm{res}}$ 与有限阈值 $\tau_j$，

$$
\bigcup_{\substack{q\in\mathcal P\\ j\in I_{\mathrm{res}}(q)}}U_{q,j}(\tau_j)
\subseteq
\{x\in U:d_j(\phi(x),\phi^\natural(x))\leq\tau_j\}.
$$

更一般地，对给定非空分量族 $J\subseteq I_{\mathrm{res}}$，

$$
\bigcup_{\substack{q\in\mathcal P\\ J\subseteq I_{\mathrm{res}}(q)}}
U_{q,J}(\boldsymbol\tau)
\subseteq
\{x\in U:\forall j\in J,\ d_j(\phi(x),\phi^\natural(x))\leq\tau_j\}.
$$

**证明**：若 $x$ 属于左侧某个路径局部保证域，则由 @h-4b5219aa3a3bbdad 得到对应分量的误差上界。对所有 $j\in J$ 同时应用即可。$\square$

> **注（与全局保证域的比较）**：路径局部证书和 @h-51e4f3855df2b936 的全局证书使用不同的残差项、路径链矩阵与代理证书，因此不能只由“路径局部”或“全局”二字比较保证域大小。在使用同一非负矩阵时，$S_{q,j}\subseteq S_j$ 与 @h-48bb46f7ef1c3c2e 给出路径共同锚点距离不小于全局共同锚点距离；保证域包含关系仍需由 @h-4c09ebab1364ae8a 这样的逐点证书上界比较推出。

路径采样增广及残差变化的比较不需要新的路径定理：在固定 $q$ 后，把 @h-59d7df4e412804c3、@h-beb567f1812b2bf2 与 @h-d2b8bdbba2123b66 中的分析域取为 $U_q$、采样集取为 $S_{q,j}$ 即可。

### #h-29524c4f0a51020c 目标网络结构的证书边界

代理网络路径是已知结构；目标网络路径不是采样数据的自动结论。若目标也给定网络表示，则可使用 @h-2058ed2f4eeaffa9 的路径交叉；若没有目标网络证书，则只能得到关于目标值的经验约束。

固定采样相容类

$$
\mathcal C=\mathcal C(\mathcal S,\mathbf y;\boldsymbol\eta,J).
$$

若需要比较具体网络表示，另固定一个**带网络证书的相容类** $\widetilde{\mathcal C}$：其元素为有序对 $(\psi,\mathcal N^\psi)$，其中 $\psi\in\mathcal C$，且 $\mathcal N^\psi$ 是 $\psi$ 在指定公共域上的有限算子网络表示。不同元素允许具有不同节点标签集。

**命题 #h-f9c6b34798128880（目标网络性质的非识别边界）**：

**(i)** 设 $P:\mathcal X_{\mathrm{op}}\to\mathrm{Prop}$ 是目标算子性质。若 $P$ 在 $\mathcal C$ 上不是常值，则当前采样数据不能唯一决定 $P$。

**(ii)** 设 $\widetilde P$ 是定义在 $\widetilde{\mathcal C}$ 上的网络证书性质。若 $\widetilde P$ 在 $\widetilde{\mathcal C}$ 上不是常值，则当前采样数据与所给容许网络证书类不能唯一决定 $\widetilde P$。

具体目标路径分划、目标 D/Z/R 标签与目标节点路径发生次数属于 (ii)；“存在某类目标网络表示”属于 (i)。代理网络在某路径、前缀或节点上的形态标签不会仅由有限采样成为目标网络的同名标签。

**证明**：(i) 即 @h-144749b31a4914e1(ii)。(ii) 中，唯一决定 $\widetilde P$ 等价于 $\widetilde P$ 在 $\widetilde{\mathcal C}$ 上为常值；非定值性正是否定。最后两句只是分别确定各性质的定义域。$\square$

若额外给出目标网络表示 $\mathcal N^\natural$，满足

$$
\phi_{\mathcal N^\natural}\equiv_U\phi^\natural,
$$

则对目标路径 $p$ 与代理路径 $q$ 定义受限路径域和交叉单元

$$
U^\natural_p=U\cap U_p^{\mathcal N^\natural},
\qquad
U_q=U\cap U_q^{\mathcal N},
\qquad
Q_{p,q}=U^\natural_p\cap U_q.
$$

对 $j\in I_{\mathrm{res}}$ 定义交叉采样集

$$
S_{p,q,j}=S_j\cap Q_{p,q},
$$

并记

$$
\mathcal R_j
=
\{(p,q):S_{p,q,j}\neq\emptyset\}.
$$

**命题 #h-8589647556e7e266（目标网络证书下的交叉采样与局部上界）**：

**(i)** 对每个 $j\in I_{\mathrm{res}}$，

$$
S_j=\bigsqcup_{(p,q)\in\mathcal R_j}S_{p,q,j}.
$$

**(ii)** 固定 $(p,q)\in\mathcal R_j$。设

$$
\mathbf L^\natural_p\in\mathscr L(c^\natural_p)\big|_{Q_{p,q}},
\qquad
\mathbf L_q\in\mathscr L(c_q)\big|_{Q_{p,q}},
$$

并定义

$$
\widehat\varepsilon_{p,q,j}
=
\sup_{x_s\in S_{p,q,j}}
d_j(c_q(x_s),c^\natural_p(x_s))
+\delta_{o,j},
\qquad
\mathbf A_{p,q}=\mathbf L_q+\mathbf L^\natural_p.
$$

则对任意 $x\in Q_{p,q}$，

$$
d_j(\phi(x),\phi^\natural(x))
\leq
D_{\mathbf A_{p,q},j}(x;S_{p,q,j})
+\widehat\varepsilon_{p,q,j}.
$$

因此，目标网络证书把代理路径局部证书进一步限制到目标路径与代理路径的交叉单元。没有目标网络表示时，$p$、$c^\natural_p$、$Q_{p,q}$ 与 $S_{p,q,j}$ 均不是当前数据中的对象。

**证明**：(i) 由 @h-1cf64e9af08b9526 的路径交叉分划与 $S_j\subseteq U$ 得到。证明 (ii)。固定 $x\in Q_{p,q}$ 与 $x_s\in S_{p,q,j}$。路径交叉分解给出

$$
\phi(x)=c_q(x),\quad
\phi^\natural(x)=c^\natural_p(x),\quad
\phi(x_s)=c_q(x_s),\quad
\phi^\natural(x_s)=c^\natural_p(x_s).
$$

由三角不等式、两条路径链的 Lip 证书及分量伪度量对称性，

$$
\begin{aligned}
d_j(\phi(x),\phi^\natural(x))
&\leq
d_j(c_q(x),c_q(x_s))
+d_j(c_q(x_s),c^\natural_p(x_s))
+d_j(c^\natural_p(x_s),c^\natural_p(x))\\
&\leq
\sum_{i\in I}[\mathbf A_{p,q}]_{i\to j}d_i(x,x_s)
+\widehat\varepsilon_{p,q,j}.
\end{aligned}
$$

该式对所有 $x_s\in S_{p,q,j}$ 成立，对同一加权和取下确界即得结论。$\square$

### #h-cf8761a19059049d 代理路径零纤维的采样证伪

本节只使用代理路径链给出的零像距条件。若 @h-83287e414000b50b 的 Z 前缀与后续路径证书共同推出该条件，则可把相应结论代入下述命题；D/Z/R 标签本身不替代路径链的 Lip 或 co-Lip 证书。

**命题 #h-f10c5a09b2a2355f（路径零纤维的采样证伪）**：设 $q\in\mathcal P$，$j\in I_{\mathrm{res}}(q)$，且 $x,y\in S_{q,j}$。若

$$
d_j(c_q(x),c_q(y))=0,
$$

并且对某个有限 $\eta_j\in[0,+\infty)$ 有

$$
d_j(\phi^\natural(x),\phi^\natural(y))>2\eta_j,
$$

则代理路径链 $c_q$ 不能同时在 $x,y$ 两点上以 $d_j$-误差 $\leq\eta_j$ 拟合目标。也就是说，不可能同时有

$$
d_j(c_q(x),\phi^\natural(x))\leq\eta_j,
\qquad
d_j(c_q(y),\phi^\natural(y))\leq\eta_j.
$$

若某个代理 Z 前缀证书推出上述零像距条件，则同一证伪结论适用于经过该前缀并满足条件的采样点对。

**证明**：前半部分是 @h-3e5f85a33b1d1e28 对代理路径链 $c_q$ 的代入。最后一句只是在零像距条件由 Z 前缀证书推出时，把该条件代入前半部分。$\square$

> **注（R 态与下界证书）**：R 态的定义只含输入尺度与零化极径条件，不含 co-Lip 下界条件。涉及下界传播时须另行给出具体 co-Lip 证书；路径级 K 证书的继承见 @h-d64105c6ec192365。

### #h-e03ec937349d6e08 节点路径发生与采样定位

设 $\beta\in V$，沿用 @h-374f884cd4d69e88 的出现重数 $m_q(\beta)$，记经过 $\beta$ 的可达路径集合为

$$
\mathcal P[\ast\beta\ast]
:=
\{q\in\mathcal P:m_q(\beta)>0\}.
$$

该节点的路径发生次数为

$$
\operatorname{occ}_{\mathcal N}(\beta)
=
\sum_{q\in\mathcal P}m_q(\beta).
$$

**定义（节点相关采样集）**：对 $j\in I_{\mathrm{res}}$，定义

$$
S_{\beta,j}
=
\bigcup_{q\in\mathcal P[\ast\beta\ast]}S_{q,j}.
$$

该集合只记录哪些第 $j$ 分量采样点的代理求值路径经过节点 $\beta$。

**命题 #h-8755da176b66e52b（节点相关采样的路径刻画）**：对每个 $j\in I_{\mathrm{res}}$，

$$
S_{\beta,j}
=
\{x_s\in S_j:m_{p_\mathcal N(x_s)}(\beta)>0\}.
$$

特别地，若 $x_s\in S_j$ 且 $p_\mathcal N(x_s)\notin\mathcal P[\ast\beta\ast]$，则 $x_s\notin S_{\beta,j}$。

**证明**：由 $S_{\beta,j}$ 的定义，$x_s\in S_{\beta,j}$ 当且仅当存在 $q\in\mathcal P[\ast\beta\ast]$ 使 $x_s\in S_{q,j}$。路径域分划使 $x_s$ 的代理路径唯一，因此该条件等价于 $m_{p_\mathcal N(x_s)}(\beta)>0$。特例由等式直接得到。$\square$

> **注（节点相关采样的作用范围）**：$S_{\beta,j}$ 只按代理路径是否经过 $\beta$ 对终端采样点分类。节点局部误差还需要目标中间态证书，或需要把终端误差通过路径链证书限制到该节点；这些条件不包含在 $S_{\beta,j}$ 的定义中。

> **注（逐次代入）**：若把同一代理算子重复求值，则只有落在 $U$ 内的迭代点才具有本章的代理路径。对每个落入相应路径保证域的迭代点，@h-4b5219aa3a3bbdad 可逐点代入；这不从一次路径证书推出后续迭代仍位于 $U$ 或保证域中。需要链级保域与误差递推时，应使用 @h-c9dea98a2f95fb0c 的完整前提。

代理网络把经验拟合结论限制到路径与节点上。代理路径分划给出路径局部残差、共同锚点距离与保证域证书；路径零纤维和节点相关采样给出代理侧的采样证伪与定位。若目标网络表示也被给出，目标路径与代理路径的交叉单元进一步承载交叉采样和局部经验上界。有限采样本身不识别目标网络结构，因此目标路径、目标节点、目标 D/Z/R 标签与其他表示层性质只能来自目标端网络证书，或来自带网络证书相容类上的不变性。

----
*[OE] ⊢ [GLENZLI] ⊢ [卷 03] ⊢ [14-empirical-network-fitting] ⊢ [7b4a3064449cb5f5]*
