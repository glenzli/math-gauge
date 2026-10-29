# 作者参考：稠密观测与完成域上的整族恢复

所有主目标均成立。作者为 AI，人工审查 pending；本文件的正确性审查、Lean 编译和候选模型校准是不同证据。目前没有候选模型试跑。

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
这正是所要求的紧集上一致收敛。取有限交是滤子公理；这里没有对无穷多个点选取一个共同尾部。Lean 使用同样假设层级下的等度连续族“紧集上点态与一致收敛等价”定理完成此步骤。

最后设 $u\to a$ 沿 $\mathcal F$。直接估计
\[
d_Y(\widehat f_i(u(i)),F(a))
\leq Kd_{\widehat X}(u(i),a)
  +d_Y(\widehat f_i(a),F(a)).
\]
右侧两项都趋零，所求同步极限成立。这个证明不要求 $u(I)$ 包含在某个紧集。

## 错误中间断言的见证

以下均用于审核中间推理，不是对真主目标的反例。

1. **整族在全域上一致 Cauchy 或一致收敛。** 取 $I=\mathbb N$、$\mathcal F$ 为尾滤子，$X=Y=\mathbb R$、$D=\mathbb Q$，
   \[
   f_n(x)=\max(0,1-|x-n|).
   \]
   这些函数均为 $1$-Lipschitz。每个固定点最终不在支撑内，故点态趋零；但 $f_n(n)=1$，所以全域一致收敛失败。当 $|m-n|>2$ 时两个尖峰相离，族在全域也非一致 Cauchy。原题只要求每个紧集上的一致收敛。

2. **原空间就是完整的恢复域。** 取 $X=D=\mathbb Q$、$Y=\mathbb R$，每个 $f_i$ 都是自然包含，任取真滤子。全部假设成立，而 $\widehat X\cong\mathbb R$；无理数处的恢复值不能解释成一个原域中的输入点。

3. **任意指标滤子都可由可数共尾序列代替。** 令 $S$ 不可数，$I$ 为 $S$ 的所有有限子集，按包含定向，取其尾滤子。任一序列 $F_n\in I$ 的并至多可数，选 $s\notin\bigcup_nF_n$，则序列从未进入尾部 $\{F:s\in F\}$，因此没有共尾序列。令 $X=Y$ 为单点空间、$f_F=0$，主假设仍全部满足。不能用“任取共尾序列”证明本题的全滤子结论。

4. **点态 Cauchy 已保证整个函数族的点态值集相对紧。** 令 $I=\mathbb N$，$\mathcal F$ 为由 $\{0\}$ 生成的主滤子，$X=D$ 为单点，$Y=\mathbb R$，$f_n(*)=n$。每个函数是 $0$-Lipschitz，推前滤子等于点 $0$ 的主滤子，故是 Cauchy 且极限为零；但整个值集 $\mathbb N$ 无界，当然非相对紧。直接把整族放入 Arzelà–Ascoli 紧性定理会缺条件。参考使用的点态到紧上一致的等度连续结论不要求整个值集相对紧，也不抽取子网。

上述第 3 项不禁止利用度量空间中序列构造 $\widehat f_i$，只禁止把任意 $\mathcal F$ 的收敛义务擅自改为一个共尾序列的收敛义务。第 4 项也不否认可以用其他已满足假设的正确紧性路线；只审查实际适用条件。

## 来源和难度边界

公开来源见 `sources.local.json`：Mathlib 的度量完备化、共享 Lipschitz 常数的等度连续性，以及等度连续族的紧集上一致收敛。稠密 Cauchy 数据、任意真滤子、完成域和移动输入组合为本题独立设计，证明独立撰写。当前未校准，不能凭参考长度称其必然更难。正确调用满足全部假设的已知结果、给出更短的完整证明，均应通过。
