KEEP

本轮复核维持上一版全部结论，未修改任何答案或证明。重点断言中的存在性命题为假；这与上一版 S5 的“不存在”一致。

反证：设存在这样的开区间 \(J\ni\alpha_*\)、有限 \(s\ge0\) 与有限 \(C\)。取 \(J\) 内任一有理数 \(p/q\)（可要求在 \(J\) 内部），令 \(k=(q,-p)\ne0\)。由无理数在 \(J\) 中稠密，可取无理数 \(\alpha\in J\) 满足
\[
0<\left|\alpha-\frac pq\right|<\frac{1}{4\pi C\,q\,\langle k\rangle^s}.
\]
取 \(u=e_k\)。则 \(u\in C_0^\infty(\mathbb T^2)\)，\(\|u\|_{L^2}=1\)，且
\[
\|N_\alpha u\|_{H^s}
=2\pi|\alpha q-p|\,\langle k\rangle^s
=2\pi q\left|\alpha-\frac pq\right|\langle k\rangle^s
<\frac1{2C}.
\]
于是
\[
C\|N_\alpha u\|_{H^s}<\frac12<1=\|u\|_{L^2},
\]
与所要求的一致估计矛盾。因此不存在这样的 \(J,s,C\)。

其余各阶段复核依据：

- S1：逆算子仍为
  \[
  (N_\alpha|_{H_N})^{-1}F
  =\sum_{0<|k|\le N}\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}e_k,
  \]
  且
  \[
  \bigl\|(N_\alpha|_{H_N})^{-1}\bigr\|_{\mathcal L(H^r,H^r)}
  =\frac1{2\pi\min_{0<|k|\le N}|\alpha k_1+k_2|}.
  \]
- S2：由
  \[
  \widehat{u-u_N}(k)
  =\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}
  \qquad(|k|>N)
  \]
  及 \(|k|>N\) 时 \(\langle k\rangle^{-q}\le(1+N^2)^{-q/2}\)，得到题述截断误差界。
- S3：仍由
  \[
  \widehat{u_\alpha-u_\beta}(k)
  =\frac{\widehat F(k)}{2\pi i}
  \frac{(\beta-\alpha)k_1}
  {(\alpha k_1+k_2)(\beta k_1+k_2)}
  \]
  及 \(|k_1|\le N\)、两个小除数均不小于 \(\delta\)，得到
  \[
  \|u_\alpha-u_\beta\|_{H^r}
  \le \frac{|\alpha-\beta|N}{2\pi\delta^2}\|F\|_{H^r}.
  \]
- S4：可逆性仍为“\(\alpha\) 为无理且非 Liouville”；全部 Sobolev 损失由
  \[
  \mathcal S(\alpha)
  =\left\{s\ge0:\inf_{q\ge1}q^s\|\alpha q\|_{\mathbb Z}>0\right\}
  \]
  给出。对 \(\alpha_*=\sqrt2-1\)，有 \(|(\sqrt2-1)k_1+k_2|\ge c/\langle k\rangle\)，故
  \[
  \mathcal S(\alpha_*)=[1,\infty),
  \]
  最小损失 \(s_{\min}=1\) 且取到；Pell 近似说明 \(s<1\) 不可能。\(C^m\to C^{m+4}\) 估计仍由
  \[
  |\widehat{N_{\alpha_*}^{-1}F}(k)|\le C|k|\,|\widehat F(k)|
  \]
  和二维格点 \(\sum_{k\ne0}|k|^{-3}<\infty\) 成立。
- S5：如上，重点断言不成立。
- S6：上一版构造的同一个
  \[
  F=\sum_{n=1}^\infty 2\pi i\lambda_n e_{k_n},
  \qquad
  k_n=(10^{n!},-p_n),\quad
  \lambda_n=\alpha 10^{n!}-p_n,
  \]
  仍为光滑零均值函数；其形式解在 \(k_n\) 处满足 \(\widehat u(k_n)=1\)，故无光滑零均值解。

因此上一版全文仍为完整答卷，本轮无需修改。