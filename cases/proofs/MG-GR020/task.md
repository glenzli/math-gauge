# 对称分解的归一化与算术边界

请按 S 编号逐项作答。所有阶段均必答；给出所要求的证明、构造或分类。判断命题时，给出结论及完整证明或满足全部前提的反例。援引前项或标准定理时说明实际适用条件。无需 Lean。



## S1 实矩阵的兼容归一化

设 E_i,F_i 为 R^d 上两组完整对称正交幂等分解，V 可逆且 VE_i=F_iV。构造正交 U 仍满足 UE_i=F_iU，并证明 U^{-1}V 对称正定。

## S2 二可逆时的完备环构造

改设 R 为特征零完备离散赋值环，极大理想 m，2∈R×。保留两组分解与 V，并要求 V≡I mod m。构造 U≡I mod m、UᵀU=I、UE_i=F_iU。

## S3 全部比较的参数群

在已有至少一个符合题目全部要求的 U_0 时，刻画所有 U。特别说明正交、模 m 同余和与各 E_i 交换的条件如何同时出现在自由度中。

## S4 整体对象与全部恢复目标

判定下面所列目标在给定条件下是否成立。若成立，完成全部构造、分类与性质的证明；若不成立，给出满足全部给定条件的反例。

设 $R$ 为特征零的完备离散赋值环，极大理想为 $\mathfrak m$，完备性相对于 $\mathfrak m$ 进拓扑。取正整数 $d,r$。给定 $M_d(R)$ 中两组矩阵 $(E_i)_{i=1}^r$、$(F_i)_{i=1}^r$，满足

$$E_i^{\mathsf T}=E_i,\qquad E_iE_j=\delta_{ij}E_i,\qquad \sum_{i=1}^rE_i=I_d,$$

$$F_i^{\mathsf T}=F_i,\qquad F_iF_j=\delta_{ij}F_i,\qquad \sum_{i=1}^rF_i=I_d.$$

又给定 $V\in\operatorname{GL}_d(R)$，使

$$V\equiv I_d\pmod{\mathfrak m},\qquad VE_i=F_iV\quad(1\le i\le r).$$

为这两组分解建立保持标准对称双线性形式的整体比较：构造 $U\in\operatorname{GL}_d(R)$，使

$$U\equiv I_d\pmod{\mathfrak m},\qquad U^{\mathsf T}U=I_d,\qquad UE_i=F_iU\quad(1\le i\le r).$$

给出构造与完整论证，并刻画所有此类比较之间的自由度。

## S5 二进环中的更深同余

设 R=Z_2，两组分解如 S4，另给 V≡I mod 8 且 VE_i=F_iV。判定是否总能构造 U≡I mod 2、UᵀU=I、UE_i=F_iU。

## S6 二维一参数的完整分类

在 Z_2 中取 c∈2Z_2，P=diag(1,0)，v=(1,c)ᵀ，Q=vvᵀ/(1+c²)，V=((1,−c),(c,1))。对分解 (P,I−P)、(Q,I−Q)，准确刻画哪些 c 存在 U≡I mod2 的正交交织矩阵，并给存在时的构造与不存在时排除全部 U 的理由。
