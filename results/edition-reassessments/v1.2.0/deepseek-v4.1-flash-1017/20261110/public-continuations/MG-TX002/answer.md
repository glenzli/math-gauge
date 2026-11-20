下面给出完整终稿。结论是：题中的映射正是矩形偏序集上的标准 rowmotion；它的一个已知的 homomesy 定理（轨道平均值定理）恰好适用于题中要求的反链大小统计量。证明分两步：先把题中映射与 rowmotion 精确对应，再陈述该定理及其全部适用条件和结论。

## 1. 题中映射就是 rowmotion

记
\[
P=[a]\times[b].
\]
若 \(I\subseteq P\) 是序理想，则它的极大元素集合
\[
\operatorname{Max}(I)
\]
是反链。反过来，若 \(A\subseteq P\) 是反链，则
\[
I(A)=\{u\in P:\ u\leq v\text{ 对某个 }v\in A\}
\]
是序理想。

事实上，
\[
\operatorname{Max}(I(A))=A. \tag{1}
\]
这是因为：

- 每个 \(v\in A\) 属于 \(I(A)\)，所以它不可能大于 \(I(A)\) 中的另一个与它可比的元素；
- 若某些 \(u,v\in A\) 满足 \(u\leq v\)，由反链定义只能有 \(u=v\)；
- 任意 \(u\in I(A)\setminus A\) 都满足 \(u<w\) 对某个 \(w\in A\)，故不是极大元素。

因此
\[
I\longmapsto \operatorname{Max}(I),\qquad
A\longmapsto I(A)
\]
给出了矩形 \(P\) 的全部序理想与全部反链之间的双射，并且两个映射彼此互逆。

现在，对序理想 \(I\subseteq P\)，标准 rowmotion 定义为
\[
\rho(I)
:=\downarrow\operatorname{Min}\bigl(P\setminus I\bigr), \tag{2}
\]
也就是由补集 \(P\setminus I\) 的全部极小元素向下生成序理想。

若题中的反链是 \(A=\operatorname{Max}(I)\)，那么按照题目的映射，
\[
R(A)=\operatorname{Min}(P\setminus I).
\]
再下生成序理想，即
\[
I(R(A))
=
\downarrow\operatorname{Min}(P\setminus I)
=
\rho(I).
\]
结合 (1)，得到
\[
R=\operatorname{Max}\circ\,\rho\circ I. \tag{3}
\]
另一方面，
\[
I(R(A))=\rho(I(A)). \tag{4}
\]
因此，在“反链 \(\leftrightarrow\) 序理想”这个双射下，题中的置换 \(R\) 与 rowmotion \(\rho\) 对应；它定义在反链上的轨道，与 rowmotion 定义在序理想上的轨道一一对应，并且轨道长度也相同。

还要核对被统计的对象。若 \(I\) 对应反链 \(A=\operatorname{Max}(I)\)，那么
\[
|A|=|\operatorname{Max}(I)|.
\]
所以题中要求的轨道平均反链大小，正是矩形 rowmotion 轨道上“序理想极大元素个数”的轨道平均。

## 2. 矩形 rowmotion 的 homomesy 定理

这里使用一个标准定理。它通常称为 **Propp–Roby 在乘积链上的 rowmotion homomesy 定理**；其原始论文为：

> James Propp and Tom Roby, *Homomesy in products of two chains*.

没有写成普通的“平均不变量”，这里要使用定理的逐轨道形式。

**定理（矩形情形）。** 设
\[
P=[m]\times[n]
\]
是两个非空有限链的乘积，采用坐标偏序；令 \(J(P)\) 为其全部序理想的集合，\(\rho\) 如 (2) 定义。若 \(\mathcal O\subseteq J(P)\) 是 \(\rho\) 的任意一条轨道，则
\[
\boxed{
\frac1{|\mathcal O|}
\sum_{I\in\mathcal O}
|\operatorname{Max}(I)|
=
\frac{mn}{m+n}.
}
\tag{5}
\]
特别地，这个平均值与轨道 \(\mathcal O\) 的选择无关。

定理中的适用条件在本题完全满足：

- \(m=a,n=b\) 都是正整数；题面甚至给定 \(a,b\geq2\)；
- 偏序正是两个有限链 \([a]\) 和 \([b]\) 的乘积偏序；
- \(\rho\) 正是题中 \(R\) 在序理想一侧的共轭；
- 被统计的量是序理想极大元素个数，也就是对应反链的大小。

应用定理时，取 \(m=a,n=b\)。

## 3. 化回题中的反链轨道

设题中 \(R\) 的一条轨道为
\[
\mathcal A=\{A_1,A_2,\ldots,A_L\}.
\]
令
\[
I_t=I(A_t).
\]
由 (3) 和 (4)，\(\rho(I_t)=I(A_{t+1})\)，所以
\[
\mathcal I=\{I_1,\ldots,I_L\}
\]
是矩形 rowmotion 的一条轨道，且有
\[
\operatorname{Max}(I_t)=A_t,
\qquad
|\operatorname{Max}(I_t)|=|A_t|.
\]
对 \(\mathcal I\) 应用定理 (5)，得到
\[
\frac1L\sum_{t=1}^L|A_t|
=
\frac1L\sum_{t=1}^L|\operatorname{Max}(I_t)|
=
\frac{ab}{a+b}.
\]
由于 \(\mathcal A\) 是任意一条题中轨道，这就证明了：
\[
\boxed{
\frac1{|\mathcal O|}
\sum_{A\in\mathcal O}|A|
=
\frac{ab}{a+b}
}
\]
对每一条轨道 \(\mathcal O\) 都成立。

## 4. 旧稿修正与自评

保留的内容：

- 题中映射与 rowmotion 的对应关系；
- 反链与其下生成序理想之间的双射；
- 用 \(|\operatorname{Max}(I)|\) 统计反链大小、把题目化为 rowmotion 轨道统计的方向；
- 原先是正确的矩形成分和最终目标公式。

新增或修正的内容：

- 明确了题中 \(R(A)\) 只是 rowmotion 作用后序理想的极大反链；
- 不再把旧稿中“边界块必然逐格扫过”的直观解释当作完整计数证明；
- 将原先缺失的轨道计数部分替换为明确的 Propp–Roby homomesy 定理，并写清定理的适用条件和逐轨道结论；
- 不再额外依赖“每个轨道的周期都等于 \(a+b\)”这一未被单独证明的辅助命题。这里使用的是定理的逐轨道平均值形式，不需要另行证明周期性质。

仍未完成或不确定的部分：

- 本稿认可并使用了题面允许援引的标准定理，没有重新给出该定理的全部原始证明。因此，这属于B2/R0的完成方式，而不是额外完成一项新的研究增量；本稿不主张R1、R2或R3。

自评：

- **MC：** 正确解释了题中映射、反链与序理想的对应，并准确使用矩形 rowmotion homomesy 定理得到原结论。
- **RMC：** 没有把未证明的局部扫描图形当作证明；没有把等价定理误写成别的情形。
- **SMC：** 在允许引用标准数学定理的前提下，原题的完整结论已交付。
- **B/R：** 原题层面的证明完整，**B2/R0**。