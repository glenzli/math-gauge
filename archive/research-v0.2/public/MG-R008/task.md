# 逐层记录的统一承载对象

给定有限秩自由阿贝尔群的逆向塔

$$P_0\xleftarrow{\rho_0}P_1\xleftarrow{\rho_1}P_2\xleftarrow{\rho_2}\cdots.$$

对 $m\ge n$，记 $\rho_{n,m}:P_m\to P_n$ 为过渡映射的复合，且 $\rho_{n,n}=I$。对每个阿贝尔群 $A$，定义

$$F(A)=\varinjlim_{n\ge0}\operatorname{Hom}_{\mathbb Z}(P_n,A),$$

其中过渡为 $u\mapsto u\rho_n$。具体地，一个记录由 $(n,u)$ 表示；$(n,u)$ 与 $(m,v)$ 相同，当且仅当存在 $r\ge n,m$ 使 $u\rho_{n,r}=v\rho_{m,r}$。记录在共同层相加。群同态 $a:A\to B$ 通过后复合诱导 $F(a):F(A)\to F(B)$。

建立这些逐层记录的统一表示理论。目标是从塔构造一个阿贝尔群 $P$，使所有 $A$ 上均有自然同构

$$F(A)\cong\operatorname{Hom}_{\mathbb Z}(P,A),$$

并使记录对有限图表中的相容条件保持一致：对任意有限图表 $D:J\to\mathbf{Ab}$，典范比较映射

$$F\!\left(\varprojlim_{j\in J}D(j)\right)
\longrightarrow\varprojlim_{j\in J}F(D(j))$$

应为同构。请给出主定理、构造及完整论证。
