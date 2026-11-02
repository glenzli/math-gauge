# 整族恢复、固定点与一致性的范围：逐阶段参考与判准

本组 version 0.1.0；AI 作者自查完成，human pending。未调用候选模型，未为本组生成或编译 Lean。既有母题参考只作为本组完整数学论证的来源，不继承其模型成绩或形式化覆盖。每阶段均 mandatory；分值用于诊断，整组 pass 必须全部阶段实质完成。

## S1 紧域上的整族极限

判定：true。

各推前滤子真且 Cauchy，由完备性有唯一 f(x)。两点同滤子取距离极限得 d(fx,fy)≤Kd(x,y)。给 ε>0，取 δ=ε/[4(K+1)] 的有限球网 x_1,…,x_m；每个中心最终误差<ε/2，有限交仍在 F。该交上任一 x 与某中心距离<δ，由两次 Lipschitz 估计得误差<2Kδ+ε/2<ε。无需抽取子网。

判准：逐点真 Cauchy 极限；有限网给全域一致。

## S2 恢复与固定点

判定：true。

紧度量 X 完备非空，各映射及极限为 q 压缩，Banach 不动点定理给唯一固定点。d(x_i,x_*)≤d(f_i(x_i),f_i(x_*))+d(f_i(x_*),f(x_*))≤q d(x_i,x_*)+sup_Xd(f_i,f)。故误差≤sup_Xd(f_i,f)/(1−q)，S1 使之趋零。sup 有限，因为两连续映射的距离在紧域上有界。

判准：唯一固定点；完整定量误差。

## S3 同步复合的极限

判定：true。

S1 分别给 f_i→f、g_i→g 的一致极限。对 x，d(g_i(f_i x),g(fx))≤L d(f_i x,fx)+d(g_i(fx),g(fx))，故 sup_X误差≤L sup_Xd(f_i,f)+sup_Yd(g_i,g)→0。若 X 空结论空真；Y 空且有 f_i 时 X 必空，按空函数解释。估计没有把变化的 f_i x 当成预先固定点。

判准：先分别恢复；正确同步误差界。

## S4 整体对象与全部恢复目标

判定：true。

## 完整证明

先给出每个 $\widehat f_i$ 的实际构造。若 $\iota x_n\to a\in\widehat X$，共同 Lipschitz 不等式使 $(f_i(x_n))$ 为 $Y$ 中的 Cauchy 列，定义
\[
\widehat f_i(a)=\lim_n f_i(x_n).
\]
$Y$ 的完备性给出存在性。用两列逼近同一点时，$d_Y(f_i(x_n),f_i(x_n'))\leq Kd_X(x_n,x_n')\to0$，所以定义无关。对两个点取逼近列并取极限，得到同一个常数 $K$ 的 Lipschitz 不等式。稠密性和 $Y$ 的分离性保证连续延拓唯一。这里用于构造空间完备化值的序列与指标滤子 $\mathcal F$ 无关；未把 $\mathcal F$ 替换成一个序列。

集合 $\iota(D)$ 在 $\widehat X$ 中稠密。固定 $a\in\widehat X$ 和 $\varepsilon>0$，取 $d\in D$ 满足
\[
d_{\widehat X}(a,\iota d)<\frac{\varepsilon}{4(K+1)}.
\]
由 $d$ 处的 Cauchy 假设，存在 $B\in\mathcal F$，使得对所有 $i,j\in B$，
\[
d_Y(f_i(d),f_j(d))<\varepsilon/2.
\]
故对 $i,j\in B$，
\[
\begin{aligned}
d_Y(\widehat f_i(a),\widehat f_j(a))
&\leq Kd(a,\iota d)+d_Y(f_i(d),f_j(d))+Kd(\iota d,a)\\
&<\varepsilon.
\end{aligned}
\]
于是 $(i\mapsto\widehat f_i(a))_*\mathcal F$ 是 Cauchy 滤子。它非平凡，因为 $\mathcal F$ 非平凡。因此 $Y$ 的完备性和分离性给出唯一极限，记为 $F(a)$。这对全部 $a$ 定义了 $F$，并且原来的稠密观测趋于 $F(\iota d)$。空域情形的映射与所有结论由空函数唯一性给出。

对任意 $a,b\in\widehat X$，沿同一个滤子取极限：
\[
d_Y(F(a),F(b))
=\lim_{\mathcal F}d_Y(\widehat f_i(a),\widehat f_i(b))
\leq Kd_{\widehat X}(a,b).
\]
故 $F$ 是 $K$-Lipschitz。若另一个连续映射 $G$ 具有所要求的稠密观测极限，真滤子在度量空间中的极限唯一性给出 $F(\iota d)=G(\iota d)$ 对所有 $d\in D$ 成立；再由密度和连续性得 $F=G$。

固定紧集 $C\subset\widehat X$ 和 $\varepsilon>0$。空集情形无须论证。以半径 $\delta=\varepsilon/[4(K+1)]$ 的球覆盖 $C$，取有限子覆盖，球心为 $a_1,\ldots,a_m\in C$。每个球心已有整族点态收敛，所以存在 $B_j\in\mathcal F$，在 $B_j$ 上
\[
d_Y(\widehat f_i(a_j),F(a_j))<\varepsilon/2.
\]
有限交 $B=\bigcap_{j=1}^m B_j$ 仍属于 $\mathcal F$。若 $i\in B$、$a\in C$，选择覆盖 $a$ 的球，则
\[
\begin{aligned}
d_Y(\widehat f_i(a),F(a))
&\leq Kd(a,a_j)
 +d_Y(\widehat f_i(a_j),F(a_j))
 +Kd(a_j,a)\\
&<\varepsilon.
\end{aligned}
\]
这正是所要求的紧集上一致收敛。取有限交是滤子公理；这里没有对无穷多个点选取一个共同尾部。

最后设 $u\to a$ 沿 $\mathcal F$。直接估计
\[
d_Y(\widehat f_i(u(i)),F(a))
\leq Kd_{\widehat X}(u(i),a)
  +d_Y(\widehat f_i(a),F(a)).
\]
右侧两项都趋零，所求同步极限成立。这个证明不要求 $u(I)$ 包含在某个紧集。

判准：Construct the unique K-Lipschitz extensions from X to its actual metric completion for every index.；From Cauchy pushforward filters only on D, construct the unique K-Lipschitz recovery on the completion under the original arbitrary proper filter.；Prove convergence of the full indexed family uniformly on every compact subset of the completion.；Establish the synchronized moving-input limit for every u:I→completion(X) tending to a along the same filter.。

## S5 全完成域的一致性

判定：false。

否。I=N 取尾滤子，X=Y=R、D=Q、K=1，f_n(x)=max(0,1−|x−n|)。每个函数是 1-Lipschitz，每个固定 x 最终值零，故全部稠密观测 Cauchy，恢复 F≡0。R 已完备，但 sup_R|f_n−F|=1，因为 f_n(n)=1。移动点 n 不趋于有限 a，因此也不反驳 S4 的移动输入结论。

判准：全部原条件与全域一致收敛失效；不误用移动输入定理。

## S6 全有界子集

判定：true。

成立。对 ε>0 用全有界性取有限 δ 网，δ=ε/[4(K+1)]，可取中心在 A；空 A 自动成立。每个中心的点态收敛由 S4 给出，有限交得到共同滤子事件。再以 f̂_i 和 F 同一个 K 的 Lipschitz 界进行两端估计，即得误差<ε。并不需要 A 自身完备或闭，也不必把 A 宣称为紧集；其闭包在完整 X̂ 中确实紧是另一条有效路线。

判准：有限网论证或紧闭包证明；不强加 A 闭。
