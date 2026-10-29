# 参考审核：复形记录的稳定消元

原强目标为假。约化记录为零只说明边界在闭链空间中稠密，不提供稳定的原像或二阶算子的有界逆。下述推导区分已经成立的 Hilbert 分解与需要闭值域的稳定消元。

## 实际成立的分解

令 $B_j=\overline{\operatorname{ran}d_{j-1}}$、$Z_j=\ker d_j$。由 $d_jd_{j-1}=0$ 及连续性有 $B_j\subset Z_j$。两者均闭，故

$$H_j=B_j\oplus\mathcal H_j\oplus Z_j^\perp,
\qquad\mathcal H_j=Z_j\cap B_j^\perp=\ker d_j\cap\ker d_{j-1}^*.$$

由 $(\operatorname{ran}A^*)^\perp=\ker A$，取正交补得到 $Z_j^\perp=\overline{\operatorname{ran}d_j^*}$。于是这是带闭包的正交 Hodge 分解。$R_j$ 等距对应 $\mathcal H_j$，因而题设给出 $\mathcal H_j=0$。

同时

$$\langle L_jx,x\rangle=\|d_{j-1}^*x\|^2+\|d_jx\|^2,$$

所以 $\ker L_j=\mathcal H_j=0$。这个等式没有给出统一正下界 $c\|x\|^2$；正算子单射与有界可逆不是同一结论。

## 一条边就足够的合法反例

取 $r=1$，$H_0=H_1=\ell^2(\mathbb N_{\ge1})$，

$$d_0(x_1,x_2,\ldots)=(x_1,x_2/2,x_3/3,\ldots).$$

该算子有界、范数 $1$、单射；有限支撑向量都在其像内，所以像稠密。故 $R_0=0$，且 $R_1=H_1/\overline{\operatorname{ran}d_0}=0$，所有题设成立。

若存在目标中的 $s_1$，两端的等式分别给出 $s_1d_0=I$ 与 $d_0s_1=I$。对标准基 $e_n$，前式迫使 $s_1e_n=ne_n$，与有界性矛盾。甚至 $y=(1/n)_n\in\ell^2$ 也没有 $d_0$ 的原像，因为其唯一形式原像是常数序列 $1$。

这里 $L_0=L_1=\operatorname{diag}(1/n^2)$，零核但没有有界逆；$\|L_je_n\|\to0$。把零核或零调和部分当成谱隙，正是失败的步骤。

## 稳定消元的精确边界

在题设的约化无环类别中，存在有界链收缩 $s$ 当且仅当所有 $\operatorname{ran}d_j$ 闭。

必要性：若 $x\in\ker d_j$，链收缩等式给出 $x=d_{j-1}s_jx$。因此 $\ker d_j=\operatorname{ran}d_{j-1}$，后者闭。

充分性：闭值域与 $R_j=0$ 给出 $\operatorname{ran}d_{j-1}=Z_j$。限制

$$d_{j-1}:Z_{j-1}^\perp\longrightarrow Z_j$$

是 Hilbert 空间间的有界双射，故逆有界。定义 $s_j$ 为先正交投影到 $Z_j$，再作用此逆。于是 $d_{j-1}s_j$ 是到 $Z_j$ 的正交投影，而 $s_{j+1}d_j$ 是到 $Z_j^\perp$ 的正交投影，两者之和为恒等。

同样的有界逆估计在 $Z_j^\perp$ 控制 $d_j$，在 $Z_j$ 控制 $d_{j-1}^*$，给出 $\langle L_jx,x\rangle\ge c_j\|x\|^2$。由正自伴性，$L_j$ 的像闭且稠密，因而满射，得到有界 $G_j=L_j^{-1}$。链关系给出 $d_jL_j=L_{j+1}d_j$，从而 $d_jG_j=G_{j+1}d_j$；于是 $s_j=d_{j-1}^*G_j$ 也满足链收缩公式。有限层数使各个有界常数可取一个有限最大值。这是增加闭值域后的结果，不能回填为原题条件。

## 原条件下的正则化结果

将各层组成有限直和 $H$，记总微分为 $D$，则 $D^2=0$，$L=DD^*+D^*D$ 是有界非负自伴算子且 $\ker L=0$。对 $\varepsilon>0$ 定义

$$G_\varepsilon=(L+\varepsilon I)^{-1},\qquad s_\varepsilon=D^*G_\varepsilon.$$

由 $DL=LD$ 得

$$Ds_\varepsilon+s_\varepsilon D=L(L+\varepsilon I)^{-1}.$$

谱定理中标量函数 $t/(t+\varepsilon)$ 在 $t>0$ 趋于 $1$，绝对值至多 $1$；$\ker L=0$ 排除零点谱投影。对每个固定向量，支配收敛给出右侧强收敛到恒等。这里每个 $s_\varepsilon$ 有界，不意味着范数随 $\varepsilon\downarrow0$ 一致有界，也不提供精确链收缩。在上述对角反例中，$\|I-L(L+\varepsilon I)^{-1}\|=1$ 对所有 $\varepsilon>0$ 成立。

## 来源与审核范围

背景核对：[Arnold–Falk–Winther 的 Hilbert 复形与闭值域分析](https://arxiv.org/abs/0906.4325)。题面只使用有界有限复形，避开无界算子的定义域额外问题；对角反例及等价条件在本稿直接证明。AI 数学审核；人工待定；尚未 Lean 形式化。
