# 局部分裂、有限呈示与截面拼接

请按 S 编号逐项作答。所有阶段均必答；给出所要求的证明、构造或分类。判断命题时，给出结论及完整证明或满足全部前提的反例。援引前项或标准定理时说明实际适用条件。无需 Lean。



共有设定：本组所有模均为幺 R 模，模之间箭头均 R 线性；R 为含幺交换环。

## S1 幂等理想商的截面

设 R 为含幺交换环，e²=e，C=R/eR，q:B→C 满射。选 b∈B 使 q(b)=1̄，构造一个 R 线性截面，证明公式与商代表无关，并得到 B≅ker q⊕C。

## S2 有限生成理想的局部检验

设 I⊂R 有限生成，B 有限秩自由，q:B→R/I 满射，且每个素点的 q_p 都分裂。证明 I=eR 对某幂等 e，并构造整体截面。

## S3 全部截面的自由度

对任意短正合列 0→A --ι→ B --q→ C→0，只要已存在一截面 s_0，证明全部截面与 Hom_R(C,A) 自由且传递对应；并刻画所有与 ι,q 相容的 B≅A⊕C 同构。

## S4 整体对象与全部恢复目标

判定下面所列目标在给定条件下是否成立。若成立，完成全部构造、分类与性质的证明；若不成立，给出满足全部给定条件的反例。

设 $R$ 为含幺交换环，给定 $R$ 模的短正合列

$$0\longrightarrow A\xrightarrow{\iota}B\xrightarrow{q}C\longrightarrow0,$$

其中 $B$ 为有限秩自由模，$C$ 为循环模。对每个素理想 $\mathfrak p\subset R$，记 $R_{\mathfrak p}$ 及 $M_{\mathfrak p}=R_{\mathfrak p}\otimes_R M$ 为通常的局部化。假设每个局部化商映射均存在 $R_{\mathfrak p}$ 线性右逆：

$$\exists s_{\mathfrak p}:C_{\mathfrak p}\longrightarrow B_{\mathfrak p},
\qquad q_{\mathfrak p}s_{\mathfrak p}=I_{C_{\mathfrak p}}.$$

把这些素点上的分裂组织为整体实现：构造 $R$ 线性映射 $s:C\to B$，满足 $qs=I_C$，并由此得到与 $\iota,q$ 相容的同构 $B\cong A\oplus C$。刻画所有整体分裂的自由度，并给出完整论证。

## S5 只保留幂等理想等式

若 I 是任意理想且 I²=I，判定 R→R/I 是否必有 R 线性截面。

## S6 给定相容的开集截面

设 f_1,…,f_m 生成单位理想，q:B→C 为 R 模满射。对每个 j 给实际的 R_{f_j} 线性截面 s_j，且在每个 R_{f_if_j} 上二者相同。不要求 C 有限呈示，判定这些截面是否唯一拼成 R 线性截面。
