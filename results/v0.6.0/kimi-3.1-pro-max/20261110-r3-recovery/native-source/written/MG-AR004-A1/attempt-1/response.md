## 总评

**这份答卷不能判定为正确、完整。**  
S3、S4、S6 基本正确；S1 的等化子证明主干正确，但关于 \(S_i\) 非开子概形的论述含有假断言；S2 的图追逐正确，但取极限前的余终性没有充分说明。**最严重的问题在 S5：用于证明关键单射性的“稠密开限制单射”和“\(F\) 是 Zariski 分离预层”均为假命题，导致 S5 的主要证明失效。**这不等于 S5 的最终命题本身为假，而是答卷没有证明它。

---

## S1：等化子部分基本正确，开性说明有错误

### 等化子证明

先对开覆盖使用层等化子，再对滤过指标系取余极限，并利用 \(\mathrm{Ab}\) 中滤过余极限与有限等化子、有限积交换，这一思路正确。左端用
\[
(U_1,\dots,U_n)\longmapsto U_1\cup\cdots\cup U_n
\]
得到 \(\Sigma\)-邻域系中的余终性，也正确。中间项和交叉项分别收敛到相应的 \(G(S_i)\)、\(G(S_i\times_SS_j)\) 的结论可以成立。

### “不是开子概形”的论证有问题

答卷声称：

> 当 \(\dim\mathcal O_{X,x_i}\ge1\) 时，\(\mathcal O_{X,x_i}\) 作为 \(\mathcal O_{X,\Sigma}\)-代数不是有限生成的。

这是假的。取
\[
X=\mathbb A^1_k,\qquad x_1=0,\quad x_2=1,\quad A=k[t],
\]
并令 \(B=M^{-1}A\)。则两点局部维数均为 \(1\)，但
\[
B_{(t)}=B\!\left[\frac1{t-1}\right].
\]
所以 \(B_{(t)}\) 是有限生成 \(B\)-代数，并且
\[
S_1=\operatorname{Spec}B_{(t)}=D(t-1)\subset S
\]
确实是开子概形。更简单地，若 \(n=1\)，则 \(S_i=S\)，更不可能据此断言非有限生成。

拓扑论证中还有一处逻辑缺漏：由“高度 \(1\) 素理想无穷多，而非零 \(f\) 只属于有限多个高度 \(1\) 素理想”，只能直接选出满足 \(f\notin\mathfrak q\) 的 \(\mathfrak q\)，**不能同时推出 \(\mathfrak q\not\subset\mathfrak p_i\)**；后一条件需要额外的素回避论证或具体构造。

因此，“\(S_i\) 不必为开子概形”这一存在性结论虽正确，但答卷所给的一般性判据和证明不能按原文接受，应改用明确的非开例子。

---

## S2：图追逐正确，但滤过极限的余终性说明不足

底部正合列化为
\[
0\longrightarrow G(S)\longrightarrow G(S_1)\oplus G(S_2)
\xrightarrow{\delta_G}G(S_1\times_SS_2)
\]
是正确的：对角逐项自动相容，\((2,1)\) 项与 \((1,2)\) 项给出同一条件。

后半部分的四引理式图追逐也正确：中间竖箭头为同构、右竖箭头为单射、两行正合，确实推出 \(\eta_S\) 为同构。

缺漏在于：答卷直接声称，对满足正合性的“好覆盖”取余极限，就得到
\[
\varinjlim H(U)=H(S_1),\qquad
\varinjlim H(V)=H(S_2),\qquad
\varinjlim H(U\cap V)=H(S_1\times_SS_2).
\]
这里必须证明这些好覆盖在全部覆盖对 \((U,V)\) 的指标系中**余终**，并且好覆盖系自身是滤过的；不能只写“随着 \(U,V\) 收缩”。题设的收缩性质可以用来补这一步，但答卷没有明确验证。因此这是可修补的证明缺漏，而不是图追逐本身的错误。

---

## S3：正确

对任意 \(\Sigma\)-邻域 \(V\)，取
\[
U=V\cap W
\]
即得 \(U\subset W\)、\(\Sigma\subset U\)、\(U\subset V\)。这证明所需余终性。

两个方向的映射分别由包含函子和
\[
\mathcal F(V)\longrightarrow\mathcal F(V\cap W)
\]
诱导，并互为逆映射的论证也正确，给出了预层余极限间的典范同构。

---

## S4：结论和反例正确

取
\[
X=\mathbb A^1_k,\qquad \Sigma=\{0\},\qquad W=X\setminus\{0\}.
\]
则 \(W\) 是稠密开集，但不存在开集 \(U\) 同时满足
\[
0\in U,\qquad U\subset W.
\]
故所考察的邻域族为空，不可能在非空的全部 \(\Sigma\)-邻域系中余终。

答卷补充的判别也正确：对固定的 \(W\)，该族非空且在全部 \(\Sigma\)-邻域中余终，当且仅当 \(\Sigma\subset W\)；充分性正是 S3。

---

## S5：存在实质性错误，最终同构没有得到证明

### 1. “稠密开限制单射”是假命题

答卷断言：对任意连通光滑整概形 \(Y\) 和稠密开集 \(W\subset Y\)，
\[
F(Y)\longrightarrow F(W)
\]
都是单射。

可用满足原题假设的 \(F\) 直接反驳。取
\[
F=\mathrm{CH}^1,
\]
在光滑概形上即 \(F(Y)=\operatorname{Pic}(Y)\)。有限对应
\(\alpha\subset Y\times Z\) 通过通常的
\[
c\longmapsto (p_Y)_*\bigl(\alpha\cdot p_Z^*c\bigr)
\]
作用于 Chow 群，因此 \(F\) 是带转移预层；光滑概形上的 Chow 群又具有 \(\mathbb A^1\)-同伦不变性。

现在取
\[
Y=\mathbb P^1_k,\qquad W=\mathbb A^1_k\subset\mathbb P^1_k.
\]
则
\[
F(\mathbb P^1)=\operatorname{Pic}(\mathbb P^1)\cong\mathbb Z,
\qquad
F(\mathbb A^1)=\operatorname{Pic}(\mathbb A^1)=0,
\]
所以稠密开限制映射 \(\mathbb Z\to0\) 显然不是单射。

### 2. “\(F\) 是 Zariski 分离预层”也被同一例反驳

用标准开覆盖
\[
\mathbb P^1=U_0\cup U_\infty,\qquad U_0\cong U_\infty\cong\mathbb A^1.
\]
有
\[
F(U_0)=F(U_\infty)=0,
\]
但非零类 \([\mathcal O(1)]\in F(\mathbb P^1)\cong\mathbb Z\) 在两个开集上的限制都为零。因此 \(F\) 不是分离预层。

事实上，正则局部环的 Picard 群为零，故 Picard 预层在各点的茎均为零，其 Zariski 层化为零层；于是
\[
\operatorname{Pic}(\mathbb P^1)\cong\mathbb Z\longrightarrow0
\]
也直接说明“\(F(U)\to F_{\mathrm{Zar}}(U)\) 对所有 \(U\) 单射”的一般断言不成立。

此外，即使只有稠密开限制单射，也不能按答卷所写推出任意开覆盖意义下的分离性；开覆盖的并通常是 \(Y\) 本身，而不是一个可替代覆盖条件的真稠密开集。

### 3. 对 S5 证明的影响

S2/四引理方法必须在右端使用
\[
F(T)\longrightarrow F_{\mathrm{Zar}}(T)
\quad\text{单射},\qquad T=S_1\times_SS_2
\]
及其归纳推广。答卷正是通过上述假的整体分离性来获得这些单射。因此：

- \(n=2\) 时，右竖箭头的单射性没有被证明；
- 四引理的前提不齐；
- 后续归纳步同样失去依据。

第3节中写出的公式
\[
s=\Phi^*(s|_W)
\]
也没有补清对象关系：若 \(\Phi\in\mathrm{Cor}(C,W)\)，它给出的是 \(F(W)\to F(C)\)，而左边原来取的是 \(s\in F(Y)\)。在未说明 \(C=Y\) 以及局部构造如何回到 \(Y\) 时，该等式并未定义，更不能替代所缺的证明。

第2节所引的层化定理，即使完全接受，也只给出 \(F_{\mathrm{Zar}}\) 的转移结构和同伦不变性等性质，**不能推出上述单射性或 Mayer–Vietoris 正合性**。

### 4. 任意点集与归纳法还有遗漏

原题允许 \(\Sigma\) 含非闭点及可比较的点，答卷却直接按 \(|\Sigma|\) 作为 \(S\) 的闭点数进行归纳。比如
\[
X=\mathbb A^1_k,\qquad \Sigma=\{\eta,0\},
\]
其中 \(\eta\) 为一般点，则
\[
(0)\cup(t)=(t),\qquad S=\operatorname{Spec}k[t]_{(t)}
\]
只有一个闭点，而 \(|\Sigma|=2\)。完整论证应先说明：删去那些自动被其他所选点的邻域包含的点，不改变 \(S\) 和邻域余极限，然后再按 \(S\) 的闭点归纳。答卷没有作这一约化；分组版 S1、分组后的 MV 正合行也只是宣称而未证明。

因此，**S5 的最终结论可能成立，但这份答卷没有建立它，且其核心证明路线中包含可被明确反例推翻的断言。**

---

## S6：两部分均正确

反例中每阶段都是
\[
\mathbb Z\xrightarrow{\times2}\mathbb Z,
\]
故每阶段都有 \(H_0\cong\mathbb Z/2\mathbb Z\)，从不正合。过渡映射在两个分量上均为乘以 \(2\)，满足链映射条件。余极限为
\[
\mathbb Z\!\left[\frac12\right]
\xrightarrow{\times2}
\mathbb Z\!\left[\frac12\right],
\]
而乘以 \(2\) 在 \(\mathbb Z[1/2]\) 中是同构，所以余极限复形正合。这正确否定了“余极限正合蕴含最终各阶段正合”。

第二问中，无论用
\[
H_n(\varinjlim_i C^{(i)})
\cong\varinjlim_iH_n(C^{(i)})
\]
还是直接元素追逐，均正确使用了“每个同调类在某后阶段变为零”的条件，证明完整。

---

**最终判断：S3、S4、S6 可接受；S1、S2 有局部需修补之处；S5 的关键证明不成立，因此整份答卷不满足“正确、完整”的要求。**