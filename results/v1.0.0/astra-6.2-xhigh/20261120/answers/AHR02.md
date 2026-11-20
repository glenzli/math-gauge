**两个包含式都证明正确，但现有全局定理比正文多要求了一项前提。** 正文只需为相应并集中出现的路径选取有效的 Lip 矩阵。Lean 的三个全局声明都要求 `hLq` 对**每一条可达路径**成立，包括没有相关样本的路径。因此，若已给出全路径证书，实现完整覆盖两个结论；若只给出正文用到的证书，则还需从附件的局部定理补一步。[正文的证书设定](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR02/physical-1/work/source.md:89) · [正文推论](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR02/physical-1/work/source.md:242)

**源码已经证明的部分**

- 分量定理从左侧取出一条路径 \(q\)，同时得到 \(j\in I_{\rm res}(q)\) 和 \(x\in U_{q,j}(\tau_j)\)。保证域成员资格给出 \(x\in U_q\subseteq U\)，`proxy_path_component_guarantee_error_bound` 给出 \(d_j(\phi(x),\phi^\natural(x))\le\tau_j\)。这正是右侧的两个条件。[分量定理](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR02/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:520)
- 联合定理取出的是**同一条**满足 \(J\subseteq I_{\rm res}(q)\) 的路径。对非空 \(J\)，Lean 联合保证域中的“\(x\in U_q\) 且每个 \(j\in J\) 都满足证书界”恰好等价于正文的交集。证明逐分量应用局部界，再用 \(c_q(x)=\phi(x)\) 得到代理的真实误差界。`_text` 封装也列出了全局可评估性、有限阈值和 \(J\) 非空；底层包含式在这些限制以外也成立，所以证明中没有用到它们。[联合定理](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR02/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:552) · [正文封装](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR02/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:588)

**全路径 `hLq` 确实可能取不到。** 取单分量空间 \(X=\{\bot,a,b,c\}\)，令 \(U=V^*=\{a,b,c\}\)。在 \(U\) 上，把 \(\{a,b\}\) 和 \(\{c\}\) 作为两个零距类，类间距离为 \(1\)。令 \(\bot\) 到自身距离为零、到其余点距离为无穷。这满足附件的扩展伪度量公理。

取两个执行一步即终止的节点。输入 \(c\) 走路径 \(p\)，输出 \(c\)；输入 \(a,b\) 走路径 \(q\)，分别输出 \(a,c\)。各节点在其余输入上输出 \(\bot\)。令代理为该网络的读出，目标在 \(U\) 上恒等于 \(c\) 并保持 \(\bot\)。只采样 \(c\)，取 \(\delta_o=\tau=0\)。目标与路径 \(p\) 均可取零矩阵，且 \(c\) 处的共同锚点距离、路径残差和真实误差都是零。因此正文左侧为 \(\{c\}\)，右侧为 \(\{b,c\}\)；取 \(J\) 为单元素集也得到同一包含式。

路径 \(q\) 没有样本，不参与上述并集。但若它有 Lip 系数 \(L\)，将 `IsLipMatrix` 用于输入对 \(a,b\) 就得到
\[
1=d(c_q(a),c_q(b))\le L\,d(a,b)=L\cdot0=0.
\]
在 `ENNReal` 中即使 \(L=\top\)，也有 \(\top\cdot0=0\)。所以这个例子满足正文所需的证书条件，却无法实例化现有全局定理的 `hLq`。

**可补齐的部分。** 分量版把 `hLq` 限定到满足 \(j\in I_{\rm res}(q)\) 的路径，联合版限定到满足 \(J\subseteq I_{\rm res}(q)\) 的路径即可。矩阵族仍可写成全路径上的函数，在其余路径任意赋值。证明从左侧取出见证 \(q\) 时已经取得相应的可评估性条件，可立即取得该路径的证书，调用现有的分量或联合局部定理，再由 \(U_q\subseteq U\) 收尾。另一个全路径前提 `hpathV` 已由正文的 \(U_q\subseteq U\subseteq V^*\) 保证。这个弱前提版本是由附件可推出的结论，三个全局声明本身均保留了较强的 `hLq`。[分量局部定理](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR02/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:155) · [联合局部定理](/private/tmp/math-gauge-astra62-xhigh-api-20261120/sessions/AHR02/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:244)

原文与所审 Lean 实现出自 Zhe Li（Glen Li / glenzli）的 *The Operator Evolution Theory*。以上为对附件版本的静态源码审阅。[作品主页](https://glenzli.com/books/oet/) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)