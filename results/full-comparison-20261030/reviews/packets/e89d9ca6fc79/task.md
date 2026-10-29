# 三份同余记录的整体恢复

在 ZFC 中工作。设 $R$ 为任意含幺环，$M$ 为左 $R$-模，$A,B,C$ 为 $M$ 的三个子模。令
\[
P=\{(x,y,z)\in M^3:x-y\in A+B,\ x-z\in A+C,\ y-z\in B+C\},
\qquad E=A\times B\times C\subseteq P,
\qquad Q=P/E.
\]
记录 $[(x,y,z)]\in Q$ 的一个原始实现是满足
\[
t-x\in A,\qquad t-y\in B,\qquad t-z\in C
\]
的元素 $t\in M$。

记
\[
I=A\cap B\cap C,\qquad L=(A\cap B)+C,\qquad
H=(A+C)\cap(B+C),
\]
并将
\[
O=\{[h]_L:h\in H\}
\]
视为 $M/L$ 的子模。对角记录给出映射
\[
j:M/I\longrightarrow Q,\qquad [t]_I\longmapsto[(t,t,t)].
\]

构造由这些数据决定的 $R$-线性映射 $\delta:Q\to O$，使
\[
0\longrightarrow M/I\xrightarrow{j}Q\xrightarrow{\delta}O\longrightarrow0
\]
为短正合序列，并满足对每个 $h\in H$ 都有
\[
\delta([(0,0,-h)])=[h]_L.
\]
同时据此确定任一记录是否有原始实现，并在有实现时描述其全部原始实现。
