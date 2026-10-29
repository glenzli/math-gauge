这样的相容分裂总存在。其全体构成以
\[
\operatorname{Hom}_{kG}(C,A_\infty)
\]
为平移空间的非空仿射空间；一般来说，它没有在所有塔的自同构下不变的规范选择。

先构造一组相容分裂。对 \(n\le m\)，记
\[
\alpha_{n,m}=\alpha_n\cdots\alpha_{m-1},\qquad
\beta_{n,m}=\beta_n\cdots\beta_{m-1},
\]
并令 \(\alpha_{n,n}\)、\(\beta_{n,n}\) 为恒等映射。使用题设给出的分裂 \(u_n\)，设
\[
V_n=\operatorname{Hom}_{kG}(C,A_n).
\]
第 \(n\) 层的每个 \(G\) 等变分裂都唯一写为 \(u_n+i_nv\)，其中 \(v\in V_n\)。

由于
\[
q_n\bigl(\beta_{n,m}u_m-u_n\bigr)=0,
\]
存在唯一的 \(d_{n,m}\in V_n\) 使
\[
i_nd_{n,m}=\beta_{n,m}u_m-u_n.
\]
特别地，第 \(m\) 层所有等变分裂经 \(\beta_{n,m}\) 送到第 \(n\) 层后，其相对于 \(u_n\) 的坐标构成仿射子空间
\[
D_{n,m}
=d_{n,m}+\{\alpha_{n,m}v:v\in V_m\}
\subseteq V_n.
\]
这些子空间非空，且对固定的 \(n\) 递减：
\[
D_{n,n}\supseteq D_{n,n+1}\supseteq D_{n,n+2}\supseteq\cdots.
\]
\(V_n\) 有限维，所以任何严格下降都会使维数降低；因此这一序列最终稳定。记其稳定值为 \(E_n\)，它是非空仿射子空间。

定义仿射映射
\[
\rho_n:V_{n+1}\longrightarrow V_n,\qquad
\rho_n(v)=d_{n,n+1}+\alpha_nv.
\]
由复合关系，对每个 \(m\ge n+1\) 有
\[
\rho_n(D_{n+1,m})=D_{n,m}.
\]
取 \(m\) 足够大，使两边均已稳定，得到
\[
\rho_n(E_{n+1})=E_n.
\]
于是可任取 \(v_1\in E_1\)，再逐层选取 \(v_{n+1}\in E_{n+1}\) 使
\[
v_n=d_{n,n+1}+\alpha_nv_{n+1}.
\]
令
\[
s_n=u_n+i_nv_n.
\]
则 \(q_ns_n=I_C\)，并且
\[
\beta_ns_{n+1}
=u_n+i_n(d_{n,n+1}+\alpha_nv_{n+1})
=s_n.
\]
这便构造出所需的一组 \(G\) 等变相容分裂。此论证直接使用等变映射空间，因此也适用于 \(\operatorname{char}k\) 整除 \(|G|\) 的情况。

令
\[
s_\infty:C\longrightarrow B_\infty,\qquad
s_\infty(c)=(s_n(c))_{n\ge1}.
\]
相容性保证该映射良定义，且 \(q_\infty s_\infty=I_C\)。现在定义
\[
\Phi_s:A_\infty\oplus C\longrightarrow B_\infty,\qquad
\Phi_s(a,c)=i_\infty(a)+s_\infty(c).
\]
这是 \(G\) 等变线性映射。它的逆可直接写出：对 \(b=(b_n)\in B_\infty\)，令 \(c=q_\infty(b)\)。各层的 \(q_n(b_n)\) 都等于 \(c\)，故
\[
a_n=i_n^{-1}(b_n-s_n(c))
\]
有定义；由 \(b\) 和 \(s\) 的相容性，\((a_n)\in A_\infty\)。因此
\[
\Phi_s^{-1}(b)
=\left(\bigl(i_n^{-1}(b_n-s_nq_\infty(b))\bigr)_{n\ge1},
q_\infty(b)\right).
\]
特别地，\(\Phi_s(a,0)=i_\infty(a)\)，而 \(q_\infty\Phi_s(a,c)=c\)，所以它给出题设要求的直和同构。

为刻画自由度，设 \((\widetilde s_n)\) 是另一组相容分裂。逐层存在唯一的 \(t_n\in V_n\) 使
\[
\widetilde s_n=s_n+i_nt_n.
\]
两组分裂的相容性等价于
\[
t_n=\alpha_nt_{n+1}\qquad(n\ge1).
\]
反过来，任何满足这些关系的 \((t_n)\) 都产生另一组相容分裂。而相容族 \((t_n)\) 恰好对应于
\[
t:C\longrightarrow A_\infty,\qquad t(c)=(t_n(c))_{n\ge1},
\]
即对应于 \(\operatorname{Hom}_{kG}(C,A_\infty)\) 的元素。因此所有相容分裂构成该向量空间的挠空间。若 \(\widetilde s_n=s_n+i_nt_n\)，则相应直和坐标之间的关系为
\[
\Phi_{\widetilde s}
=\Phi_s\circ
\begin{pmatrix}I&t\\0&I\end{pmatrix}.
\]

最后考虑整塔的交换图同构。设另一塔记为带撇的对象，并有同构
\[
F_n^A:A_n\to A_n',\qquad F_n^B:B_n\to B_n',
\qquad F^C:C\to C',
\]
它们与各短正合列及全部过渡映射交换。则分裂被输送为
\[
s_n^F=F_n^B\,s_n\,(F^C)^{-1}.
\]
这仍是一组相容分裂；若原分裂平移 \(t\)，其平移量输送为
\[
t_n^F=F_n^A\,t_n\,(F^C)^{-1}.
\]
所以塔同构诱导分裂挠空间之间的仿射同构，其线性部分由上述公式给出。

更具体地，若在目标塔上另选相容分裂 \(r'\)，记塔同构诱导的逆极限映射为 \(F_\infty^A,F_\infty^B\)，则
\[
\delta=(i_\infty')^{-1}
\bigl(F_\infty^B s_\infty-r_\infty'F^C\bigr)
\in\operatorname{Hom}_{kG}(C,A_\infty')
\]
良定义，并且在两组直和坐标中
\[
\Phi_{r'}^{-1}F_\infty^B\Phi_s
=
\begin{pmatrix}
F_\infty^A&\delta\\
0&F^C
\end{pmatrix}.
\]
当 \(r'=s^F\) 时，\(\delta=0\)。

规范选择一般不存在：对任意 \(t=(t_n)\in\operatorname{Hom}_{kG}(C,A_\infty)\)，映射
\[
H_n^B=I_{B_n}+i_nt_nq_n
\]
与恒等的 \(A_n\)、\(C\) 映射一起给出整塔的自同构；其逆为 \(I_{B_n}-i_nt_nq_n\)。它把每组分裂送到 \(s_n+i_nt_n\)。因此，只要 \(\operatorname{Hom}_{kG}(C,A_\infty)\ne0\)，就没有被所有塔自同构固定的分裂；该空间为零时，相容分裂唯一，因而自动不变。