# 递归系统的固定族、稳定分支与终止

版本 0.1.2。以下全部阶段均须作答。

设 $\mathcal X^\circ=\mathcal X\setminus\{\bot\}\ne\varnothing$，$d_1,\ldots,d_m$ 是 $\mathcal X$ 上的扩展伪度量，$m\ge1$，且 $d_i(x,\bot)=+\infty$ 对 $x\ne\bot$ 成立。记 $\mathbf d=(d_1,\ldots,d_m)^{\mathsf T}$，扩展非负实数运算采用 $0\cdot(+\infty)=0$。

给定有限有向多重图 $(V,E)$，$V\ne\varnothing$。每个节点 $v$ 配有非空集合 $U_v\subseteq\mathcal X^\circ$，并有分割

$$
U_v=S_v\sqcup\bigsqcup_{e:s(e)=v}D_e.
$$

在 $S_v$ 上给定输出映射 $h_v:S_v\to\mathcal X^\circ$。每条边 $e:v\to w$ 配有输入转移 $b_e:D_e\to U_w$ 和返回算子 $a_e:\mathcal X\to\mathcal X$，满足 $a_e(\bot)=\bot$、$a_e(\mathcal X^\circ)\subseteq\mathcal X^\circ$，以及

$$
\mathbf d(a_e(y),a_e(z))\le L_e\mathbf d(y,z)
\qquad(y,z\in\mathcal X^\circ),
$$

其中 $L_e$ 是给定的有限值非负 $m\times m$ 矩阵。不等式按分量理解。以节点为块指标，令

$$
M_{vw}=\sum_{e:v\to w}L_e,
\qquad \rho(M)<1.
$$

对算子族 $F=(F_v:U_v\to\mathcal X^\circ)_{v\in V}$，定义一次展开

$$
(\mathcal TF)_v(x)=
\begin{cases}
h_v(x),&x\in S_v,\\
a_e\bigl(F_w(b_e(x))\bigr),&x\in D_e,\ e:v\to w.
\end{cases}
$$

算子族之间采用诱导规范

$$
\Delta_{v,i}(F,G)=\sup_{x\in U_v}d_i(F_v(x),G_v(x)).
$$

逐 S 编号交付。证明题须写出论证；判断题须明确结论并给证明或完整核验反例；构造题须验证所需性质。援引此前结果或标准定理时，说明其条件在当前阶段为何适用。各阶段的附加条件只在该阶段明确指定的范围内生效。未完成内容请明确标记。

## S1　展开的比较

在上述条件下证明Δ(TF,TG)≤MΔ(F,G)及其n步版本。构造仅由M决定的正权重ω和q∈(0,1)，使Mω≤qω，并给出Dω(F,G)=max_{v,i}Δv,i(F,G)/ωv,i的收缩界。

## S2　有界完整输出空间

另假设d=max_i d_i在X°上是有限值完备度量，且直径有限。构造唯一非吸收固定族F*，并证明对每个初始族H，存在有限C_H使max Δ(TⁿH,F*)≤C_Hqⁿ。

## S3　局部数据的稳定性

在S2条件下，另有同图、同U及分割、同b的系统T̃，终止输出及返回算子分别为h̃,ã，且满足同一组L_e界。记距离向量\(\mathbf d(u,v)=(d_i(u,v))_{i=1}^m\)，区别于 S2 的标量距离 d。给有限向量η_v≥0，使终止片上\(\mathbf d(h_v(x),\widetilde h_v(x))\le\eta_v\)，且每条e:v→w及每个非吸收y都有\(\mathbf d(a_e(y),\widetilde a_e(y))\le\eta_v\)（向量不等式）。证明两固定族满足Δ(F*,F̃*)≤(I−M)⁻¹η。

## S4　原始结构的整体目标

只使用共同设定。判断是否总有唯一整体非吸收固定族，并存在仅由M决定的q∈(0,1)，使每个初始族H均有有限C_H满足max Δ(TⁿH,F*)≤C_Hqⁿ（n≥1）。

## S5　完整但无界的状态空间

设一个节点自环，X°=R、通常距离，U=D=N≥1⊂R、S=∅，b(n)=n+1，a(y)=y/2，吸收元仍被保持。求出全部非吸收固定族并判断是否唯一；再对H(n)=n判断其展开是否按全输入上确界距离趋于F⁰(n)=0。

## S6　有限残差的分支

在共同设定下，假设d=max d_i在X°上是有限值完备度量，但不要求直径有限。给H₀使R₀=Dω(TH₀,H₀)<∞。令B(H₀)={F:Dω(F,H₀)<∞}。证明该分支完备且T不变，构造其中唯一固定族并给每个H∈B(H₀)的几何误差界；说明能否据此断言所有分支共享同一固定族。

## S7　终止与偏定义解

只使用共同设定，允许构造的输出暂取X含⊥。对每个输入按b追踪唯一调用路径，构造信息序（⊥低于一切非吸收点）中的最小固定族。刻画它何时处处非吸收；再判断逐输入有限终止是否保证所有H的统一几何误差界。若所有调用路径另有共同有限终止深度上界，说明迭代何时精确，以及这是否足以得到从n≥1开始的有限常数几何误差界。
