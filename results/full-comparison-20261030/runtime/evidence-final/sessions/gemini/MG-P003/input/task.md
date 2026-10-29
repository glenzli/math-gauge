# 半局部值的层化比较

设 $k$ 为域，$\mathrm{Sm}/k$ 为光滑、分离、有限型 $k$-概形的范畴。令 $\mathrm{Cor}_k$ 为有限对应的加性范畴：对象与 $\mathrm{Sm}/k$ 相同，$\mathrm{Cor}_k(Y,Z)$ 是由 $Y\times_k Z$ 中那些在 $Y$ 的某个连通分支上有限且满射的整的闭子概形（即不可约且约化的闭子概形）生成的自由阿贝尔群，复合采用有限对应的通常交积与推前。概形态射通过其图给出有限对应。

给定加性反变函子

$$F:\mathrm{Cor}_k^{\mathrm{op}}\longrightarrow\mathrm{Ab},$$

并假设对每个 $Y\in\mathrm{Sm}/k$，投影诱导的同态

$$F(Y)\longrightarrow F(Y\times_k\mathbb A^1_k)$$

是同构。记 $F_{\mathrm{Zar}}$ 为 $F$ 的底层普通预层关于 Zariski 开覆盖的层化，$\eta:F\to F_{\mathrm{Zar}}$ 为典范态射。

设 $X$ 是光滑拟射影 $k$-概形，$\Sigma\subset |X|$ 是有限非空点集。在包含 $\Sigma$ 的一个仿射开集 $\operatorname{Spec}A$ 中，以 $\mathfrak p_x$ 表示点 $x$ 对应的素理想，置

$$M=A\setminus\bigcup_{x\in\Sigma}\mathfrak p_x,
\qquad S=\operatorname{Spec}(M^{-1}A).$$

对 $H=F$ 或 $F_{\mathrm{Zar}}$，约定

$$H(S)=\varinjlim_{\Sigma\subset U\subset X\,\text{开}}H(U),$$

其中转移映射为向更小开邻域的限制。

研究典范同态 $\eta_S:F(S)\to F_{\mathrm{Zar}}(S)$，建立它为同构的结论，并给出完整论证。
