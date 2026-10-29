# 线性记录、有限观测与原空间恢复

版本 0.1.1。以下全部阶段均须作答。

设 $E$ 为实 Banach 空间，$E'$ 为其连续对偶。以 $E'$ 的所有有限维线性子空间组成的有向集为指标，对每个 $F\subset E'$ 给定线性映射 $\lambda_F:F\to\mathbb R$。若 $F\subset G$，要求

$$\lambda_G|_F=\lambda_F.$$

已知存在有限常数 $C\ge0$，使

$$|\lambda_F(\varphi)|\le C\|\varphi\|\qquad(\varphi\in F).$$

有限观测组 $(\varphi_1,\ldots,\varphi_k)$ 的记录为
$\bigl(\lambda_F(\varphi_1),\ldots,\lambda_F(\varphi_k)\bigr)$，其中 $F$ 包含这些泛函。两个记录族之间采用距离

$$d(\lambda,\mu)=\sup_{\|\varphi\|\le1}|\lambda_{\mathbb R\varphi}(\varphi)-\mu_{\mathbb R\varphi}(\varphi)|.$$

每个有界线性算子 $T:E\to E$ 还诱导记录变换

$$\lambda^T_F(\varphi)=\lambda_{T'F}(T'\varphi),\qquad T'\varphi=\varphi\circ T.$$

逐 S 编号交付。证明题须写出论证；判断题须明确结论并给证明或完整核验反例；构造题须验证所需性质。援引此前结果或标准定理时，说明其条件在当前阶段为何适用。各阶段的附加条件只在该阶段明确指定的范围内生效。未完成内容请明确标记。

## S1　记录的完整载体

对任意题设Banach E，将兼容有界记录等距识别为E″，给出双向构造。证明规范J:E→E″线性等距，并证明记录变换λ↦λ^T在该识别下恰为T″。

## S2　可恢复记录的稳定性

假设E自反。构造所有记录的唯一原空间恢复x_λ，并证明与每个T相容。对两个有界算子T,U及两份记录λ,μ，证明‖x_(λ^T)−x_(μ^U)‖≤‖T‖d(λ,μ)+‖T−U‖‖x_μ‖。

## S3　子空间约束

在S2条件下，令Y⊂E闭线性，Y⊥={φ∈E′:φ|Y=0}。证明x_λ∈Y iff z_λ|Y⊥=0，并从记录给出dist(x_λ,Y)的准确对偶公式。

## S4　一般Banach空间

只使用共同设定，判断每份合法记录是否都有唯一x_λ∈E、‖x_λ‖≤C，实现全部记录且恢复稳定并与所有T相容。

## S5　单条记录的拓扑条件

设E任意实Banach。对一份合法记录，另假设S1的z_λ:E′→R关于弱星拓扑σ(E′,E)连续。判断它是否必可在E中实现，并给出此连续性与原空间可实现性的充要关系。

## S6　有限观测的精确匹配

设E任意实Banach，λ的统一界为C。对有限维F⊂E′，定义 q_F:E→F* 为 q_Fx(φ)=φ(x)。对每个这样的F和ε>0，证明存在x_F,ε∈E，满足q_Fx_F,ε=λ_F且‖x_F,ε‖≤C+ε。判断是否总可取ε=0，并解释该有限匹配为何不能替代S5的条件。
