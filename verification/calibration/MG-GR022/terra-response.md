记 \(v=\operatorname{ord}_t\)，并约定 \(v(0)=\infty\)、\(S/(t^0)=0\)。下面用条件

\[
\tag{B}\exists d\ge 0\quad\forall n,\ \nu_n\le d
\]

表示指数列有界。所有出现的充要条件都将归结为此条件。

## 1. 完成的坐标模型、正合性与纤维

置

\[
\mathcal T=\left\{(x_n)\in\prod_{n\ge1}S:
\forall m\ge1,\ \#\{n:x_n\notin t^mS\}<\infty\right\},
\]
以及
\[
\mathcal H=\left\{(c_n)\in\prod_{n\ge1}S/(t^{\nu_n}):
\forall m\ge1,\ 
\#\{n:c_n\notin t^m(S/(t^{\nu_n}))\}<\infty\right\}.
\]

则有自然的 \(S\) 模同构
\[
\widehat A\simeq\mathcal T,\qquad
\widehat B\simeq\mathcal T,\qquad
\widehat C\simeq\mathcal H.
\]

具体说，\(\mathcal T\) 中的 \((x_n)\) 对应第 \(m\) 层记录
\((x_n\bmod t^m)_n\)，它属于 \(\bigoplus_n R/(t^m)\)。反过来，相容记录的每个坐标确定一个 \(S\) 中的元素，而每层的有限支撑性正给出 \(\mathcal T\) 的条件。

同样，\(\mathcal H\) 中的 \((c_n)\) 对应第 \(m\) 层记录
\[
\bigl(c_n\bmod t^{\min(m,\nu_n)}\bigr)_n
\in\bigoplus_n S/(t^{\min(m,\nu_n)})
\simeq C/t^mC.
\]
相容记录的第 \(n\) 个坐标在 \(m\ge\nu_n\) 时稳定，从而恢复 \(c_n\)。

在这些模型下，令
\[
D:\prod_nS\longrightarrow\prod_nS,\qquad
D(x_n)=(t^{\nu_n}x_n).
\]
则
\[
\widehat\iota(x)=D(x),\qquad
\widehat q(x)=\bigl(x_n\bmod t^{\nu_n}\bigr)_n.
\]
此外，\(\eta_A,\eta_B\) 分别是有限支撑多项式列的嵌入；利用
\(R/(t^{\nu_n})\simeq S/(t^{\nu_n})\)，映射 \(\eta_C\) 是有限支撑列的嵌入
\[
C\simeq\bigoplus_nS/(t^{\nu_n})\hookrightarrow\mathcal H.
\]
因此 \(\eta_C\) 单射。这个描述也给 \(C\) 一个自然的 \(S\) 模结构。

定义
\[
\mathcal W=D^{-1}(\mathcal T)
=\left\{(y_n)\in\prod_nS:(t^{\nu_n}y_n)_n\in\mathcal T\right\}.
\]
于是
\[
\operatorname{im}\widehat\iota=D\mathcal T,\qquad
\ker\widehat q=D\mathcal W
=\left\{b\in\mathcal T:b_n\in t^{\nu_n}S\ \forall n\right\}.
\]

事实上，对 \(c=(c_n)\in\mathcal H\)，取每个 \(c_n\) 次数小于 \(\nu_n\) 的唯一多项式代表 \(b(c)_n\)；若 \(\nu_n=0\)，取 \(b(c)_n=0\)。则 \(b(c)\in\mathcal T\)，且 \(\widehat q(b(c))=c\)。故 **\(\widehat q\) 总是满射**，并且它的每个纤维为
\[
\boxed{\ \widehat q^{-1}(c)=b(c)+D\mathcal W.\ }
\]

在 \(\mathcal T\) 的 \(t\) 进拓扑中，
\[
\boxed{\ \overline{\operatorname{im}\widehat\iota}
=\overline{D\mathcal T}=D\mathcal W=\ker\widehat q.\ }
\]
证明时，\(D\mathcal W\) 由各坐标条件 \(b_n\in t^{\nu_n}S\) 给出，故为闭集；而对其中任意 \(b\)，其有限截断属于 \(D\mathcal T\)，并 \(t\) 进收敛到 \(b\)。

映射 \(\widehat\iota\) 总是单射。因此完成列
\[
0\longrightarrow\widehat A\xrightarrow{\widehat\iota}
\widehat B\xrightarrow{\widehat q}\widehat C\longrightarrow0
\]
只可能在中间不正合。它短正合当且仅当 **(B)** 成立：

- 若 \(\nu_n\le d\) 对所有 \(n\) 成立，则 \(D(y)\in\mathcal T\) 蕴含 \(y\in\mathcal T\)，所以 \(\mathcal W=\mathcal T\)。
- 若指数列无界，可取互异的 \(n_i\) 使 \(\nu_{n_i}\to\infty\)。令 \(y_{n_i}=1\)，其余坐标为零，则 \(y\in\mathcal W\setminus\mathcal T\)。

## 2. \(E\)、\(j\)、挠元及 \(p\) 的分裂性

由上面的模型，
\[
Q\simeq\mathcal T/D\mathcal T,\qquad
E\simeq D\mathcal W/D\mathcal T.
\]
因为 \(D\) 在 \(\prod_nS\) 上单射，得到明确的 \(S\) 模模型
\[
\boxed{\ E\simeq\mathcal W/\mathcal T,\qquad
[y]\longmapsto[Dy].\ }
\]
因此
\[
\boxed{\ E=0\quad\Longleftrightarrow\quad\text{(B)}.\ }
\]
映射 \(p\) 总是满射，且
\[
p^{-1}(c)=[b(c)]+E\qquad(c\in\mathcal H).
\]

由于 \(p\circ j=\eta_C\) 且 \(\eta_C\) 单射，\(j\) 单射。其像是 \(Q\) 中**有有限支撑代表**的类：有限支撑的 \(S\) 系数代表可逐坐标模 \(t^{\nu_n}\) 换成多项式代表。

对每个 \(r\ge1\)，有更精确的公式
\[
\boxed{\ 
Q[t^r]
=j\!\left(\bigoplus_{n\ge1}
\frac{t^{\max(\nu_n-r,0)}S}{t^{\nu_n}S}\right).
\ }
\]
因而 \(Q\) 的整个 \(S\) 模挠子模恰为 \(j(C)\)，而 \(E\) 是无挠 \(S\) 模。

证明如下。若 \(t^r y\in\mathcal T\)，则 \(y\in\mathcal T\)；故 \(\mathcal W/\mathcal T\) 没有 \(t\)-幂挠元。由于 \(S\) 的每个非零元素是单位乘以某个 \(t\) 的幂，\(E\) 无挠。

若 \(x=[b]\in Q[t^r]\)，则 \(t^rb=D(a)\)，其中 \(a\in\mathcal T\)。除有限多个 \(n\) 外 \(a_n\in t^rS\)，故对这些坐标可消去 \(t^r\)，得到 \(b_n\in t^{\nu_n}S\)。因此 \(p(x)\) 有有限支撑，即 \(p(x)=\eta_C(c)\) 对某个 \(c\in C\) 成立。由 \(t^rx=0\) 和 \(\eta_C\) 单射知 \(t^rc=0\)。于是 \(x-j(c)\in E\) 也被 \(t^r\) 杀死；由 \(E\) 无挠可知 \(x=j(c)\)。反向包含显然。

最后，
\[
\boxed{\ p\text{ 存在 }S\text{ 线性右逆}\quad
\Longleftrightarrow\quad\text{(B)}.\ }
\]
若 (B) 成立，\(E=0\)，故 \(p\) 是同构。若指数列无界，取互异的 \(n_i\)，使 \(\nu_{n_i}\ge i+1\)，并令
\[
c_{n_i}=t^{\nu_{n_i}-1}\bmod t^{\nu_{n_i}},\qquad
c_n=0\quad(n\ne n_i).
\]
则 \(c\in\mathcal H[t]\)，但 \(c\) 不是有限支撑列。若 \(p\) 有线性右逆 \(s\)，则 \(s(c)\in Q[t]=j(C[t])\)，从而 \(c\in\eta_C(C)\)，矛盾。

## 3. 商模、再次完成与拓扑

对 \(m\ge1\)，记
\[
\mathcal D_m=\bigoplus_{n\ge1}S/(t^{\min(m,\nu_n)}).
\]
坐标约化给出自然同构
\[
\boxed{\ 
Q/t^mQ\ \simeq\ \mathcal D_m\
\simeq\ \widehat C/t^m\widehat C,
\ }
\]
且在这两个同构下，\(p\) 诱导的映射就是 \(\mathcal D_m\) 的恒等映射。

为证明这一点，首先
\[
\mathcal T/t^m\mathcal T\simeq\bigoplus_nS/(t^m),
\]
其中 \(D\mathcal T\) 的像为各坐标上的
\(t^{\nu_n}S/(t^m)\)，故其商是 \(\mathcal D_m\)。另一方面，
\(\mathcal H\to\mathcal D_m\) 满射，核恰为 \(t^m\mathcal H\)：核中各坐标可选择被 \(t^m\) 整除的多项式代表，除以 \(t^m\) 后所得列仍满足 \(\mathcal H\) 的限制条件。

由于 \(\mathcal H\) 分离，上述商同构推出
\[
\boxed{\ \bigcap_{m\ge1}t^mQ=\ker p=E.\ }
\]
特别地，\(Q\) 分离当且仅当指数列有界。

相容商记录还给出
\[
\boxed{\ \widehat Q\simeq\mathcal H=\widehat C. \ }
\]
在此同构下，典范映射 \(\eta_Q:Q\to\widehat Q\) 就是 \(p\)，所以它总是满射，核为 \(E\)。此外 \(\eta_{\widehat C}:\widehat C\to\widehat{\widehat C}\) 是同构，而
\[
\boxed{\ \widehat p:\widehat Q\longrightarrow
\widehat{\widehat C}\ }
\]
在两端均识别为 \(\mathcal H\) 后是恒等映射。同样，\(\widehat j:\widehat C\to\widehat Q\) 也识别为恒等映射。

### \(E\) 自身的完成

对每个 \(m\ge1\)，令
\[
P_m=\left\{(a_n)\in\prod_nS/(t^m):
\forall d\ge0,\ 
\#\{n:\nu_n\le d,\ a_n\ne0\}<\infty\right\}.
\]
则
\[
\boxed{\ E/t^mE\simeq
P_m\Big/\bigoplus_nS/(t^m),\qquad
\widehat E\simeq
\varprojlim_m P_m\Big/\bigoplus_nS/(t^m).\ }
\]
这里 \(\mathcal W\) 模 \(t^m\) 的像正是 \(P_m\)：一个方向由 \(D(y)\in\mathcal T\) 得到；反方向只需把 \(P_m\) 的坐标提升为次数小于 \(m\) 的多项式。其核为 \(t^m\mathcal W\)，而 \(\mathcal T\) 的像为有限支撑直和。

实际上，\(E\) 自身的 \(t\) 进拓扑总是分离且完备，即
\[
\boxed{\ \eta_E:E\xrightarrow{\sim}\widehat E.\ }
\]
证明分离性：若 \(y+\mathcal T\in\bigcap_m t^mE\)，则对每个 \(m\)，\(y\bmod t^m\) 都有有限支撑，故 \(y\in\mathcal T\)。

证明完备性：在 \(\prod_nS\) 上取由 \(t^m\prod_nS\) 定义的统一 \(t\) 进拓扑。\(\mathcal T\) 在其中闭，而 \(\mathcal W=D^{-1}\mathcal T\) 也闭，故 \(\mathcal W\) 完备；并且
\[
t^m\mathcal W=\mathcal W\cap t^m\prod_nS.
\]
给定 \(E/t^mE\) 中的相容记录，可递归选择代表 \(y_m\in\mathcal W\)，使
\(y_{m+1}-y_m\in t^m\mathcal W\)。它们在 \(\mathcal W\) 中收敛，极限代表原记录，故 \(\eta_E\) 满射。

注意这里不能把 \(E\) 自身的拓扑与子空间拓扑混同。由 \(E\subseteq t^mQ\) 对所有 \(m\) 成立，\(E\) 从 \(Q\) 继承的子空间拓扑是**平凡拓扑**；而其自身的 \(t\) 进拓扑总是分离。因此
\[
\boxed{\ 
E\text{ 的两种拓扑相同}
\quad\Longleftrightarrow\quad E=0
\quad\Longleftrightarrow\quad\text{(B)}.
\ }
\]
同样，由于 \(E\subseteq t^mQ\) 对所有 \(m\) 成立，包含映射 \(E\hookrightarrow Q\) 诱导的完成映射
\[
\widehat E\longrightarrow\widehat Q
\]
总是零映射，尽管 \(\eta_E\) 本身总是同构。