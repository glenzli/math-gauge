# 超滤子代数、有限观测商与连通纤维

请按 S 编号逐项作答。所有阶段均必答；给出所要求的证明、构造或分类。判断命题时，给出结论及完整证明或满足全部前提的反例。援引前项或标准定理时说明实际适用条件。无需 Lean。



## S1 已知拓扑的有限观察商

设 X 为紧 Hausdorff 空间。令 B 为全部开闭子集，e:X→{0,1}^B 取各特征函数值，P=e(X)。证明 P 为 profinite，e:X→P 为连续满射，所有连续到有限离散空间的映射唯一因子化于 e；证明其纤维恰为连通分量。

## S2 两个空间的共同观察

对紧 Hausdorff X,Y，证明自然映射 P(X×Y)→P(X)×P(Y) 是同胚，其中 P 按 S1 构造。

## S3 连通纤维的满射

设 f:X→Y 是紧 Hausdorff 空间间连续满射，且每个 f^{-1}(y) 连通。证明 f^{-1}(C) 对 Y 的每个连通分量 C 连通，并证明 f 诱导 P(X)≅P(Y)。

## S4 整体对象与全部恢复目标

判定下面所列目标在给定条件下是否成立。若成立，完成全部构造、分类与性质的证明；若不成立，给出满足全部给定条件的反例。

采用 ZFC。对集合 $X$，记 $U(X)$ 为它的全部超滤子构成的集合，$\delta_x$ 为 $x$ 处的主超滤子。映射 $f:X\to Y$ 的推前为

$$U(f)(\mathcal F)=\{B\subseteq Y:f^{-1}(B)\in\mathcal F\}.$$

对 $\mathfrak W\in U(U(X))$，定义

$$m_X(\mathfrak W)=\{A\subseteq X:\{\mathcal F\in U(X):A\in\mathcal F\}\in\mathfrak W\}.$$

给定集合 $X$ 和映射 $a:U(X)\to X$，假设对每个 $x\in X$ 及 $\mathfrak W\in U(U(X))$ 有

$$a(\delta_x)=x,\qquad a(m_X(\mathfrak W))=a(U(a)(\mathfrak W)).$$

目标是在 $X$ 上构造唯一的紧 Hausdorff 拓扑，使每个超滤子 $\mathcal F$ 恰好收敛于 $a(\mathcal F)$，并建立这类运算与紧 Hausdorff 拓扑之间的双向对应。

该对应还应识别全部映射：若 $a:U(X)\to X$、$b:U(Y)\to Y$ 满足上述条件，则集合映射 $f:X\to Y$ 对所构造的拓扑连续，当且仅当

$$f\circ a=b\circ U(f).$$

此外，为重建出的空间构造一个 profinite 空间 $P$（紧、Hausdorff、全不连通）及连续满射 $q:X\to P$，使对每个 profinite 空间 $Z$，与 $q$ 复合给出双射

$$C(P,Z)\longrightarrow C(X,Z).$$

刻画 $q$ 的各个纤维，并用原运算 $a$ 及有限值观测给出 $q$ 为单射的充要判据。这里，对有限集合 $A$，记 $b_A:U(A)\to A$ 为将超滤子送到其中唯一单点集的点的映射；一个有限值观测是满足

$$f\circ a=b_A\circ U(f)$$

的映射 $f:X\to A$。

请给出构造、唯一性及完整论证。

## S5 代数侧的乘积构造

给满足 S4 两条代数律的 a:U(X)→X、b:U(Y)→Y。对 F∈U(X×Y) 定义 c(F)=(a(Uπ_XF),b(Uπ_YF))。证明 c 满足两条代数律，并证明其重建拓扑就是两重建拓扑的乘积；再写出它的有限观察商。

## S6 观察商同构的逆向

设 f:X→Y 为紧 Hausdorff 空间间连续满射，并且诱导 P(X)→P(Y) 为同胚。判定 f 的每个纤维是否必连通。
