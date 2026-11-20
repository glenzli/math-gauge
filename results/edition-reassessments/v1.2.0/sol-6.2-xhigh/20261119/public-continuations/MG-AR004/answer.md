## 审阅结论

待审答卷整体未达到原题的完整证明要求。S3、S4、S6 正确。S1 的等化子结论和主要证明正确，但关于局部化何时为开的断言有反例。S2 的结论与比较图正确，取滤过余极限前缺少一项可补足的余终性论证。S5 的半局部同构在题设的任意域上成立，但答卷用于证明它的全局单射性断言错误，所需的预层正合列也未建立。[原题](/private/tmp/math-gauge-neutral-revisions-gpt-20261120/engineering/sessions/sol-6.2-xhigh--MG-AR004/work/original-task.md) · [待审答卷](/private/tmp/math-gauge-neutral-revisions-gpt-20261120/engineering/sessions/sol-6.2-xhigh--MG-AR004/work/original-answer.md)

### S1　等化子成立，非开性的论证有误

答卷从有限开覆盖的层等化子取滤过余极限，这条路线成立。在共同仿射开 \(\operatorname{Spec}A\) 内，令 \(N_i=A\setminus\mathfrak p_i\)。交项 \(S_i\times_S S_j\) 的坐标环是 \((N_iN_j)^{-1}A\)，相应的主开是 \(D(f_if_j)=D(f_i)\cap D(f_j)\)。这些主开在交项的开邻域中余终。事实上，若开集的补集 \(V(I)\) 与该局部化的像不交，则 \(I\) 在局部化后生成单位理想，故 \(I\) 含有某个 \(f_if_j\in N_iN_j\)。对角项用 \(D(f_if_i)=D(f_i)\) 即可。于是答卷确实计算了所要求的交项及其限制映射，滤过余极限保持有限积和等化子给出结论。若最初指定的点有包含关系，应取其中对应于极大素理想的点作为 \(S\) 的闭点。删去其余指定点不改变邻域系统。[答卷 S1 等化子证明](/private/tmp/math-gauge-neutral-revisions-gpt-20261120/engineering/sessions/sol-6.2-xhigh--MG-AR004/work/original-answer.md:7)

第 3 节的两个一般性论断都超出了依据。在 \(\mathbb A^1_k\) 的 \(0,1\) 两点处半局部化所得环 \(R\) 中，有 \(R[1/(t-1)]=k[t]_{(t)}\)。因此即使局部环维数为 \(1\) 且有两个闭点，\(S_1\) 也可以是主开子概形。拓扑论证也有反例。取两个仿射平面的不交并，各选一个闭点，则两个局部环均为二维，各 \(S_i\) 都是开闭分支。[答卷 S1 非开性论证](/private/tmp/math-gauge-neutral-revisions-gpt-20261120/engineering/sessions/sol-6.2-xhigh--MG-AR004/work/original-answer.md:40)

原题所要的非开例子可取同一仿射平面中的 \(x_1=(0,0)\)、\(x_2=(1,0)\)。素理想 \((v-(u-1)^m)\)（\(m\ge 1\)）彼此不同，均包含于 \(\mathfrak p_{x_2}\)，且均不包含于 \(\mathfrak p_{x_1}\)。任一含 \(x_1\) 的主开，其定义元的非零多项式分子仅有有限多个不可约因子，所以该主开含有上述某个素理想对应的点。此点在 \(S_1\) 的像之外，故 \(S_1\) 的像不开放。

### S2　比较图正确，余终性需要补证

半局部概形中，每个点都是某个闭点的泛化，所以含全部闭点的开集就是整个 \(S\)。给定一对分别含 \(x_1,x_2\) 的开邻域，从各自邻域中删去另一闭点，所得二开仍覆盖 \(S\)。再应用题设的固定 \(V\) 收缩条件，就得到一对使序列正合的细化。因此正合覆盖族在全体邻域对中余终。对两个正合覆盖逐坐标取交，再应用同一条件，得到共同的正合细化，故该族是滤过的。

补上这两步，按 S1 的邻域计算取余极限，答卷的顶行成立。其图追逐也正确。中间竖箭头的同构给出局部提升，右竖箭头的单射保证提升的差为零，顶行正合将提升拼成 \(H(S)\) 的元素。[答卷 S2](/private/tmp/math-gauge-neutral-revisions-gpt-20261120/engineering/sessions/sol-6.2-xhigh--MG-AR004/work/original-answer.md:47)

### S3、S4　两项正确

S3 通过 \(V\mapsto V\cap W\) 给出余终细化，并以限制映射构造典范余极限映射的逆，适用于题设的任意反变阿贝尔群预层。S4 取 \(X=\mathbb A^1_k\)、\(\Sigma=\{0\}\)、\(W=D(t)\)，满足全部前提，而所问的邻域子族为空。答卷给出的充要条件 \(\Sigma\subseteq W\) 也正确。末尾的局部环计算适用于结构层 \(\mathcal O_X\)。[答卷 S3–S4](/private/tmp/math-gauge-neutral-revisions-gpt-20261120/engineering/sessions/sol-6.2-xhigh--MG-AR004/work/original-answer.md:99)

### S5　结论成立，提交的证明有实质错误

**成立的步骤。** 普通态射通过图定义有限对应，源不连通时取各连通分支的图之和。两截面的拉回都是投影拉回同构的逆，所以 \(\mathbb A^1\)-同伦的对应对 \(F\) 作用相同。单点情形也独立成立，因为题设的邻域余极限就是茎，层化在茎上诱导同构。[答卷 S5 的图与同伦步骤](/private/tmp/math-gauge-neutral-revisions-gpt-20261120/engineering/sessions/sol-6.2-xhigh--MG-AR004/work/original-answer.md:173) · [单点步骤](/private/tmp/math-gauge-neutral-revisions-gpt-20261120/engineering/sessions/sol-6.2-xhigh--MG-AR004/work/original-answer.md:210)

**第 3 节的全局稠密开单射性和全局分离性均为假。** 取 \(F(Y)=\mathrm{CH}^1(Y)=\operatorname{Pic}(Y)\)。这是满足题设的带转移预层。对整有限对应 \(C\subset Y\times Z\)，记投影为 \(p:C\to Y\)、\(q:C\to Z\)，其作用为
\[
L\longmapsto p_*\bigl(c_1(q^*L)\cap[C]\bigr).
\]
这是 Chow 群的有限对应作用。第一 Chern 类与精细 Gysin 交积的相容性和投影公式保证它与对应的复合相容，图对应给出通常拉回。Chow 群的同伦不变性适用于这里的光滑概形。现在沿稠密开 \(\mathbb A^1_k\subset\mathbb P^1_k\) 的限制是 \(\mathbb Z\to 0\)。而 \(\mathcal O(1)\) 在两个标准仿射开上都平凡，直接否定了分离性推论。原论证中 \(\Phi\in\mathrm{Cor}_k(C,W)\) 的拉回值属于 \(F(C)\)。即使构造出所述对应，所得等式也只涉及 \(s\) 在 \(C\) 上的限制。由全局分离性推出各局部化比较箭头单射的推导因此失效。[答卷 S5 第 3 节](/private/tmp/math-gauge-neutral-revisions-gpt-20261120/engineering/sessions/sol-6.2-xhigh--MG-AR004/work/original-answer.md:189)

**第 5 节未建立预层正合列。** 调用 S2 需要对每个给定的 \((U_0,V)\)，保持 \(V\) 固定，找出一个 \(U\subseteq U_0\)，使整个阶段序列在中间项正合。具体须证明每个限制相同的截面对都来自 \(F(S)\)。原答的移动技术描述和定理引文没有给出这一点。若 \(U,V\) 指环境概形的开邻域，邻域余极限首先提供的是阶段到余极限的映射。写出 \(F(S)\to F(U)\oplus F(V)\) 还须说明 \(U,V\) 是 \(S\) 上的开集及其取值方式。直接走极限路线也可以，但需证明每个阶段的同调类最终消亡，原答同样未证明。归纳图的层一行可用 S1 的方法对两组邻域取极限来验证，预层一行则沿用了同一缺口。[答卷 S5 第 5 节](/private/tmp/math-gauge-neutral-revisions-gpt-20261120/engineering/sessions/sol-6.2-xhigh--MG-AR004/work/original-answer.md:221)

#### 任意域上的独立核验

先说明所需的**半局部泛点单射性**。对任何同伦不变带转移预层 \(E\)，以及光滑拟射影概形的有限点半局部化 \(S\)，限制
\[
E(S)\longrightarrow\prod_{\xi\in S^{(0)}}E(k(\xi))
\]
是单射，其中 \(E(k(\xi))\) 也按开邻域余极限取值。下面给出这项标准三元组论证在本题域范围内的依据。

按分支可设代表截面的仿射邻域 \(Y\) 积分。设该截面在稠密开 \(W\subset Y\) 上为零，令 \(Z=Y\setminus W\) 取约化结构。零维情形直接成立。设 \(d=\dim Y>0\)，在无穷域上可选线性投影使 \(Y\to B\times\mathbb A^1\) 有限、\(Z\to B\) 有限，且 \(Y\to B\) 在指定点光滑，其中 \(B=\mathbb A^{d-1}\)。两个有限性条件由投影中心避开相应的无穷远闭集得到，光滑性由指定点处微分满秩得到。这些都是非空开条件。为选择投影，可先选每个指定点在 \(Y\) 中的一个闭特化，在这些闭点处满足微分条件即可。有限映射 \(Y\to B\times\mathbb A^1\) 的源为 Cohen–Macaulay，靶正则且同维，因而有限平坦。取 \(B\times\mathbb P^1\) 在 \(k(Y)\) 中的正规化，得到在 \(B\) 上射影的紧化 \(\bar Y\)。其边界有限于 \(B\)，并与同样有限于 \(B\) 的 \(Z\) 不交。

在足够小的指定点邻域 \(U\) 上，\(U\times_B\bar Y\) 中的对角截面 \(\Delta\) 是有效 Cartier 除子，因为相对曲线沿该截面光滑。取相对 ample 线丛的高次幂 \(L\)。可选取 \(s'_0\in H^0(L(-\Delta))\) 和 \(s_1\in H^0(L)\)，使两者在拉回的边界和 \(Z\) 上均不消失，并使 \(s_1\) 在边界等于 \(s_0=\delta s'_0\)，其中 \(\delta\) 是 \(\Delta\) 的定义截面。这是有限闭子概形上的插值。其上线丛在半局部底上平凡，平凡化可缩到 \(U\) 上，再用 Serre 消灭提升指定截面。线性族 \((1-t)s_0+ts_1\) 的零概形避开边界，相对 \(U\times\mathbb A^1_t\) 既射影又仿射，故有限。相对曲线的仿射部分在每个底纤维上有限平坦于仿射直线，因而是纯一维 Cohen–Macaulay 的。零概形在底纤维上有限，所以定义截面在纤维上是非零因子，给出有限平坦的零概形。它的周期给出一个有限对应同伦，两端分别是 \(\Delta+V(s'_0)\) 与 \(V(s_1)\)。除 \(\Delta\) 外，两端对应都落在 \(W\) 中。对给定截面应用同伦不变性，便知其在 \(U\) 上为零。

有限域上可分别在两个充分大、次数互素的有限扩域上满足上述非空开条件，并按扩域后的分支使用同一论证。扩域后含所有指定点原像的开邻域，可由原域的开邻域拉回细化，因为有限映射是闭映射。有限扩域的图与转置图给出拉回及转移，其复合为扩域次数乘以恒等。因此原核元素被两个互素次数同时杀死。这就给出了所需的任意域版本。

现在令 \(J=F_{\mathrm{Nis}}\)。Voevodsky 的 Nisnevich 层化定理给 \(J\) 以转移，并使 \(F\to J\) 成为带转移态射。这里所需的同伦不变性可以使用 **Druzhinin 的任意域上线性有框转移严格同伦不变性定理**。它适用于同伦不变、准稳定的线性有框预层。有限对应预层沿忘掉框架的函子满足这些条件：该函子取有限零概形的基本周期并推到源与靶的积，标准悬置对应送到恒等对应。因此 \(J\) 同伦不变，无需对 \(k\) 加完美性、无限性或系数限制。

在光滑分支的泛点，\(F(k(\xi))\to J(k(\xi))\) 是同构。原因是 Nisnevich 覆盖在该泛点有同剩余域的提升，该提升给出的有理截面可延拓到某个非空开。于是 \(F\to J\) 的逐对象核和余核都是同伦不变带转移预层，泛点值均为零。由上述半局部泛点单射性，它们在 \(S\) 上也为零。滤过余极限正合，故 \(F(S)\xrightarrow{\sim}J(S)\)。

对每个点 \(x\) 应用同一结论，得到 \(F(\mathcal O_{X,x})\cong J(\mathcal O_{X,x})\)。由于 \(F(\mathcal O_{X,x})\) 也是 \(F_{\mathrm{Zar}}\) 的茎，\(F_{\mathrm{Zar}}\to J\) 是 Zariski 层的同构。最后，在题设共同仿射开中，\(D(m)\)（\(m\in M\)）在 \(\Sigma\) 的开邻域中余终。若某个邻域的补集为 \(V(I)\)，则 \(I\) 不包含于任何 \(\mathfrak p_x\)，由有限素理想回避可取 \(m\in I\cap M\)。因此上述比较计算的正是题设的余极限，得到典范同构 \(\eta_S\)。

这也核实了原答第 2 节所述的层化性质。转移的唯一性来自 Nisnevich 层化的泛性质。关于附带的上同调比较，可对 \(q>0\) 考虑 \(Y\mapsto H^q_{\mathrm{Nis}}(Y,J)\)。带转移层的 Nisnevich 上同调具有转移，严格同伦不变性使这个预层同伦不变。正阶上同调类 Nisnevich 局部为零，故其泛点值为零。半局部泛点单射性于是使它的 Zariski 茎全为零。Zariski 与 Nisnevich 之间的高阶直像消失，Leray 给出两种上同调的一致性。上述层化性质也给出极限层面的比较，但原答仍缺少所援引的固定覆盖阶段正合性。

**“任何局部化都单射”的范围确实过大。** 取 \(k=\mathbb R\)，令 \(R=\mathbb R[u,v]_{(u,v)}\)、\(h=u^2+v^2\)、\(T=\operatorname{Spec}R[1/h]\)，并取 \(E(Y)=H^1_{\mathrm{Zar}}(Y,\mathbf K^M_2)\)。Milnor \(K_2\) 层有转移且严格同伦不变，上述上同调比较和 Nisnevich 上同调的转移使 \(E\) 满足 S5 的函子条件。其 Zariski 层化为零，因为正阶上同调类局部为零。另一方面，Milnor \(K_2\) 的 Gersten 复形在这个光滑整局部环上正合。限制到 \(T\) 时，删去唯一的余维二项 \(\mathbb Z\) 和余维一素理想 \((h)\) 的项，故
\[
E(T)\cong \mathbb Z/\partial\bigl(\kappa((h))^\times\bigr).
\]
这里 \(\partial\) 是曲线 \(h=0\) 在原点的除子阶数。其正规化在原点上方只有一支，局部环为 \(\mathbb C[v]_{(v)}\)，剩余域次数为 \(2\)，所以 \(\operatorname{im}\partial=2\mathbb Z\)。于是 \(E(T)\cong\mathbb Z/2\)，而 \(E_{\mathrm{Zar}}(T)=0\)。这反驳了对任意局部化的断言。这个 \(T\) 是主开局部化，答卷归纳图中具体纤维积的右竖箭头则仍需按其自身情形论证。

### S6　两问均正确

反例的阶段微分与过渡映射都是乘 \(2\)，确为链映射。每阶段的 \(H_0\) 为 \(\mathbb Z/2\mathbb Z\)。两项的余极限由 \([a,i]\mapsto a/2^i\) 识别为 \(\mathbb Z[1/2]\)，极限微分乘 \(2\) 为同构。第二问的两种证明均成立。阿贝尔群的滤过余极限保持核、像和余核，因而同调与其交换。每个阶段同调类最终为零，便使余极限同调为零。[答卷 S6](/private/tmp/math-gauge-neutral-revisions-gpt-20261120/engineering/sessions/sol-6.2-xhigh--MG-AR004/work/original-answer.md:255)

### 本轮修订与自评

- **保留**了前次逐项判定、S1 的正反例、S2 的余终性补证，以及 S5 的 \(\operatorname{Pic}\) 反例。
- **新增或修正**了 S1 交项的邻域识别、S5 对应作用与阶段箭头的类型检查、覆盖任意域的半局部比较论证，以及对任意局部化单射断言的反例。
- **仍未核对**的是原答引文编号的版本对应。审阅结论依据上文明确列出的定理陈述和适用条件。原答所声称的固定 \(V\) 阶段正合性仍属未证步骤，其缺口已经定位。
- **自评** 本稿完成了答卷审阅的逐项判定，给出了错误断言的反例及其依赖影响，并独立核实了 S5 的原结论。交付为本回复正文。