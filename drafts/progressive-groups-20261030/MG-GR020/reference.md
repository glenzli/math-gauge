# 对称分解的归一化与算术边界：逐阶段参考与判准

本组 version 0.1.0；AI 作者自查完成，human pending。未调用候选模型，未为本组生成或编译 Lean。既有母题参考只作为本组完整数学论证的来源，不继承其模型成绩或形式化覆盖。每阶段均 mandatory；分值用于诊断，整组 pass 必须全部阶段实质完成。

## S1 实矩阵的兼容归一化

判定：construction。

G=VᵀV 对称正定。由 VE_i=F_iV 及转置等式 E_iVᵀ=VᵀF_i 得 GE_i=E_iG。实对称谱定理定义唯一正定 H=G^{-1/2}，且 H 与每个 E_i 交换（各 G 特征子空间被 E_i 保持）。令 U=VH，则 UᵀU=HGH=I，UE_i=F_iU，且 U^{-1}V=G^{1/2} 正定。取逆与平方根都在全矩阵上定义，不逐块任意选择不相容根。

判准：Gram 与各 E_i 交换；正交性及剩余正定因子。

## S2 二可逆时的完备环构造

判定：construction。

同 S1，G=VᵀV 与 E_i 交换，Z=G−I∈mM_d(R)。定义 H=Σ_{n≥0}c_n Z^n，其中 c_n=(−1)^n binom(2n,n)/4^n∈Z[1/2]⊂R。m 进完备性使各矩阵项趋零且级数收敛。形式二项式恒等式 (Σc_nz^n)^2(1+z)=1 可逐系数在 Z[1/2] 核验，截断模 m^N 仅有限项，故 H²G=I。每项对称且与 E_i 交换，H≡I mod m。取 U=VH，得 UᵀU=I、交织与同余；行列式平方为 1，所以 U 可逆。

判准：系数属于 R；收敛及矩阵恒等式；保留全部交织。

## S3 全部比较的参数群

判定：classification。

令 H=U_0^{-1}U。由两个 U 正交得 HᵀH=I；同余给 H≡I mod m。交织给 HE_i=U_0^{-1}F_iU=E_iH。反之任意具有这三条件的 H 都使 U=U_0H 满足所需全部性质，参数唯一。因此所有解是群 G_E={H∈GL_d(R):HᵀH=I,H≡I mod m,HE_i=E_iH∀i} 的右挠子；不预先给 U_0 时不能将其称为带指定原点的群。该群保持每个 im E_i，标准形式在这些直和项间正交。

判准：两方向及唯一参数；同余条件不丢失。

## S4 整体对象与全部恢复目标

判定：false。

本题的全称目标不成立。以下反例满足完整的环、分解和给定相似变换条件，却连不加同余限制的正交比较也不存在。任意完整合法反例均可解决原目标，不要求采用本例。



## 系数环和矩阵

取 $R=\mathbb Z_2$，$\mathfrak m=2\mathbb Z_2$，$d=r=2$。这是特征零、相对于极大理想进拓扑完备的离散赋值环。由于 $5$ 是单位，以下矩阵属于 $M_2(R)$：

$$P=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad Q=\frac15\begin{pmatrix}1&2\\2&4\end{pmatrix},\qquad V=\begin{pmatrix}1&-2\\2&1\end{pmatrix}.$$

令 $E_1=P,E_2=I-P,F_1=Q,F_2=I-Q$。直接相乘得 $P^2=P$、$Q^2=Q$，而 $P,Q$ 均对称。于是两组矩阵分别构成完整的对称正交幂等分解，包括两个交叉乘积均为零。

矩阵 $V$ 的逆为

$$V^{-1}=\frac15\begin{pmatrix}1&2\\-2&1\end{pmatrix}.$$

因此 $V\in\operatorname{GL}_2(R)$，且 $V\equiv I\pmod{\mathfrak m}$。又有 $QV=VP$，因而 $(I-Q)V=V(I-P)$。所有给定条件成立。



## 等距比较的障碍

假设某个矩阵 $U$ 满足 $U^{\mathsf T}U=I$ 和 $QU=UP$。记其第一列为 $(a,b)^{\mathsf T}$。后一等式说明该列被 $Q$ 固定。由第一坐标

$$\frac15(a+2b)=a$$

得到 $2b=4a$。环 $\mathbb Z_2$ 是整环且 $2\ne0$，故 $b=2a$。另一方面，$U^{\mathsf T}U=I$ 的左上角给出

$$a^2+b^2=1,\qquad\text{从而}\qquad5a^2=1.$$

将等式映入 $\mathbb Z/8\mathbb Z$。平方的剩余类仅为 $0,1,4$，乘以 $5$ 后仅为 $0,5,4$，不可能等于 $1$，矛盾。因此不存在这样的 $U$；可逆性和 $U\equiv I\pmod{\mathfrak m}$ 甚至尚未使用。

原任务要求对每组合法数据构造等距比较，故这个合法实例已经否定全称目标；本实例的所有等距比较组成空集。不能把原任务的非空构造要求解释为只需给出一个可能为空的集合。



## 与给定相似变换的关系

本例 $V^{\mathsf T}V=5I$。对给定相似实现做归一化时，必须同时保持对称形式和对两组分解的交织关系；仅知道 Gram 矩阵是单位矩阵模极大理想，并不能推出所需的兼容归一化存在。上面的无解证明直接排除了全部正交交织矩阵，不限于对 $V$ 乘某个标量的尝试，也没有声称矩阵 $5I$ 在整个矩阵环中不存在平方根。

本参考不主张其他剩余特征下的恢复定理。若候选给出额外条件下的正确结果，可以记录为条件化贡献；它不能替代对本题原范围的处理。

判准：If refuting the universal construction, verify all coefficient-ring, decomposition, invertibility, congruence and intertwining hypotheses and prove that a requested isometric comparison does not exist.；If claiming the full construction, prove it for every permitted complete discrete valuation ring, with every displayed requirement and the stated classification of comparisons.。

## S5 二进环中的更深同余

判定：true。

成立。G=VᵀV，Z=G−I∈8M_d(Z_2)。仍用 S2 的 c_n，但现在只估赋值 v_2(c_n)≥−2n，故每项 c_nZ^n 的赋值至少 n，均整且趋零。n≥1 的各项至少在 2M_d，故 H≡I mod2。形式恒等式可在 Q_2 中逐系数核验，并以收敛 Cauchy 乘积给 H²G=I。对称、交换及 U=VH 的论证同 S2，得到全部结论。未声称 2 在 Z_2 可逆，只证明分母被 Z 的高阶整除吸收。

判准：负赋值系数与正赋值幂的总估计；所有矩阵条件。

## S6 二维一参数的完整分类

判定：classification。

V 行列式 1+c² 为奇单位，V≡I mod2，且 QV=VP。若 U 第一列为 (a,b)，QU=UP 强迫 b=ca（从固定向量在 Rv 中，第一坐标为 a）；正交性给 (1+c²)a²=1。若 c≡2 mod4，则 1+c²≡5 mod8，奇数平方≡1 mod8，不可能。若 c∈4Z_2，则 z=c²∈16Z_2；正半次二项式级数给单位 d=(1+z)^{1/2}∈1+2Z_2（系数赋值同样由 v_2≥−2n 控制，幂项至少 4n），d²=1+c²。取 U=d^{-1}V 即正交且模2为 I，并保留交织。因此精确条件为 c∈4Z_2。全部解在一个解存在后按 S3 的群描述；无解方向没有只排除标量归一化。

判准：验证原数据；模8排除所有第一列；可行 c 的收敛根构造。
