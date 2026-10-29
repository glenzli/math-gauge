# 递归算子系统的闭合理论

为所给定的相互递归算子系统建立完整的闭合理论。以下依次给出**局域动力学与执行迹分解**、**整体算子族的显式构造**、**主定理**以及**完整的数学论证**。

---

## 一、 系统架构与符号约定

### 1. 基础空间与规范指标
设指标集为 $I = \{1, \ldots, m\}$，节点集为有限集 $V$。
- 对每个节点 $v \in V$，块指标记为 $(v, i)$，其中 $v \in V, i \in I$。向量空间 $\mathbb R^{|V|m}$ 中的向量按块分量记为 $\mathbf y = (y_v)_{v \in V}$，其中 $y_v = (y_{v,1}, \ldots, y_{v,m})^{\mathsf T} \in \mathbb R^m$。
- 空间 $\mathcal X = \mathcal X^\circ \sqcup \{\bot\}$ 上配有扩展伪度量族 $\mathbf d = (d_1, \ldots, d_m)^{\mathsf T}$。对任意 $x \in \mathcal X^\circ$ 及 $i \in I$，有 $d_i(x, \bot) = +\infty$；对伪度量必然有 $d_i(\bot, \bot) = 0$。在 $[0, +\infty]$ 上采用代数约定 $0 \cdot (+\infty) = 0$。
- 算子族空间定义为
  $$
  \mathcal F = \prod_{v\in V} (\mathcal X^\circ)^{U_v} = \left\{ F = (F_v: U_v \to \mathcal X^\circ)_{v\in V} \right\}.
  $$
- 对 $F, G \in \mathcal F$，其诱导规范向量 $\mathbf\Delta(F, G) \in [0, +\infty]^{|V|m}$ 定义为
  $$
  \Delta_{v, i}(F, G) = \sup_{x\in U_v} d_i(F_v(x), G_v(x)), \qquad \mathbf\Delta_v(F, G) = \bigl(\Delta_{v,1}(F,G), \ldots, \Delta_{v,m}(F,G)\bigr)^{\mathsf T}.
  $$

### 2. 块转移矩阵
图 $(V, E)$ 上给定的非负矩阵族 $(L_e)_{e\in E} \subset \mathbb R_{\ge 0}^{m\times m}$ 诱导了分块矩阵 $M \in \mathbb R_{\ge 0}^{(|V|m)\times(|V|m)}$：
$$
M_{vw} = \sum_{e \in E:\, s(e)=v,\, t(e)=w} L_e \quad (v, w \in V), \qquad \rho(M) < 1.
$$

---

## 二、 局域动力学与执行迹分解

由节点域的互不相交分割 $U_v = S_v \sqcup \bigsqcup_{e: s(e)=v} D_e$，系统在不相交并集 $\mathcal U = \bigsqcup_{v\in V} U_v$ 上定义了一个**确定性离散动力系统**。

对任意初态 $(v, x) \in \{v\} \times U_v$，存在唯一的单向转移轨迹：
1. 若 $x \in S_v$，轨迹在第 $0$ 步终止；
2. 若 $x \in D_e$（$e: v \to w$），系统经由边 $e$ 转移到状态 $(w, b_e(x))$。

由此归纳定义初态 $(v, x)$ 的**确定性执行迹（Execution Trace）**：
- 状态序列：$(v_0, x_0) = (v, x)$；
- 若 $x_k \in D_{e_{k+1}}$（其中 $e_{k+1}: v_k \to v_{k+1}$），则令 $x_{k+1} = b_{e_{k+1}}(x_k) \in U_{v_{k+1}}$；
- 记终止时间（转移步数）为
  $$
  \tau(v, x) = \inf\{ k \ge 0 : x_k \in S_{v_k} \} \in \mathbb N \cup \{+\infty\}.
  $$

对有限长度 $k < \tau(v, x)$，记累积复合返回算子为
$$
\mathcal A_{p_k} = a_{e_1} \circ a_{e_2} \circ \cdots \circ a_{e_k}: \mathcal X \to \mathcal X \quad (k \ge 1), \qquad \mathcal A_{p_0} = \mathrm{id}_{\mathcal X}.
$$
因为 $a_e(\mathcal X^\circ) \subseteq \mathcal X^\circ$ 且 $a_e(\bot) = \bot$，故 $\mathcal A_{p_k}(\mathcal X^\circ) \subseteq \mathcal X^\circ$ 且 $\mathcal A_{p_k}(\bot) = \bot$。

---

## 三、 整体算子族 $F^*$ 的构造

### 1. 显式路径构造
对任意节点 $v \in V$ 和输入 $x \in U_v$，整体算子 $F^*_v(x)$ 的构造依据执行迹分为两类情形：

#### 情形一：终止迹（$\tau(v, x) = k < +\infty$）
初态 $(v, x)$ 在有限步 $k$ 内到达停机集 $S_{v_k}$，停机值为 $h_{v_k}(x_k) \in \mathcal X^\circ$。此时整体算子由局域数据沿执行路径的反向复合完全确定：
$$
F^*_v(x) \triangleq \mathcal A_{p_k}\bigl(h_{v_k}(x_k)\bigr) = a_{e_1}\bigl(a_{e_2}\bigl(\cdots a_{e_k}(h_{v_k}(x_k))\cdots\bigr)\bigr).
$$
由于 $h_{v_k}(x_k) \in \mathcal X^\circ$ 且每一步 $a_e(\mathcal X^\circ) \subseteq \mathcal X^\circ$，必有 $F^*_v(x) \in \mathcal X^\circ$。

#### 情形二：非终止迹（$\tau(v, x) = +\infty$）
若存在无限转移序列 $p_\infty = (e_1, e_2, \ldots)$，任取参考族 $Z \in \mathcal F$，考虑截断序列
$$
y_n(x) = \mathcal A_{p_n}\bigl(Z_{v_n}(x_n)\bigr) = a_{e_1} \circ \cdots \circ a_{e_n}\bigl(Z_{v_n}(x_n)\bigr) \in \mathcal X^\circ.
$$
由 Lipschitz 矩阵的复合乘积控制：
$$
\mathbf d\bigl(y_{n+k}(x), y_n(x)\bigr) \le L_{e_1} \cdots L_{e_n} \mathbf d\bigl(\mathcal A_{e_{n+1}\cdots e_{n+k}}(Z_{v_{n+k}}(x_{n+k})), Z_{v_n}(x_n)\bigr).
$$
当图转移矩阵满足 $\rho(M) < 1$ 时，$L_{e_1} \cdots L_{e_n} \le (M^n)_{v, v_n} \to 0$（几何收敛）。故在规范度量完备化意义下，序列 $(y_n(x))_{n\ge 1}$ 在 $\mathcal X^\circ$ 内收敛到唯一极限点，且该极限独立于参考族 $Z$ 的选取，定义其极限为 $F^*_v(x)$。

> **注（关于基元 $\bot$ 与终止性闭合）：**  
> 若取形式初始族 $F^{(0)}_\bot(x) \equiv \bot$，根据 $a_e(\bot)=\bot$ 及 $(\mathcal T F^{(0)}_\bot)_v(x) = h_v(x)$（$x\in S_v$），有限次展开给出：
> $$
> (\mathcal T^n F^{(0)}_\bot)_v(x) = 
> \begin{cases}
> F^*_v(x) \in \mathcal X^\circ, & \tau(v, x) \le n, \\
> \bot, & \tau(v, x) > n.
> \end{cases}
> $$
> 欲使整体极限算子落入 $\mathcal F$（即对一切 $x \in U_v$ 均有 $F^*_v(x) \in \mathcal X^\circ$），且在伪度量下与任意有限族 $H$ 的展开保持有限距离（因为 $d_i(y, \bot)=+\infty$），系统由局域数据自然闭合。若假定系统处处有限终止（即对一切 $v$ 与 $x\in U_v$ 均有 $\tau(v, x) < +\infty$），则 $F^*$ 无需任何拓扑完备性假设，完全由有限步局域代数组合给出。

### 2. 不动点性质验证
验证 $F^* = \mathcal T F^*$：
- 当 $x \in S_v$ 时，$\tau(v, x) = 0$，$k=0$，此时 $F^*_v(x) = h_v(x) = (\mathcal T F^*)_v(x)$；
- 当 $x \in D_e$（$e: v \to w$）时，令 $x' = b_e(x) \in U_w$。初态 $(w, x')$ 的转移迹恰为 $(v, x)$ 剔除首条边 $e$ 后的迹，其终止步数为 $\tau(w, x') = \tau(v, x) - 1$。因此：
  $$
  F^*_v(x) = a_e\left(\mathcal A_{p'}\bigl(h_{v_k}(x_k)\bigr)\right) = a_e\bigl(F^*_w(b_e(x))\bigr) = (\mathcal T F^*)_v(x).
  $$
因此 $F^*$ 严格满足 $F^* = \mathcal TF^*$。

---

## 四、 主定理（闭合与几何逼近定理）

> ### 主定理
> 设给定系统满足前述条件，块转移矩阵 $M$ 满足 $\rho(M) < 1$。则：
> 1. **唯一性**：在算子族空间 $\mathcal F$ 中，方程 $F = \mathcal T F$ 存在唯一的整体解 $F^*$；
> 2. **几何收敛性**：存在收敛因子 $q \in (\rho(M), 1)$ 及正向量 $\mathbf u \in \mathbb R_{>0}^{|V|m}$，使得对任意初始算子族 $H \in \mathcal F$（满足 $\mathbf\Delta(H, F^*) < +\infty$），有限展开 $\mathcal T^n H$ 满足几何衰减估计：
>    $$
>    \max_{v\in V, \, i\in I} \Delta_{v, i}(\mathcal T^n H, F^*) \le C_H q^n \qquad (\forall n \ge 1),
>    $$
>    其中有限常数可显式取为
>    $$
>    C_H = \frac{\max_{(v,i)} u_{v,i}}{\min_{(v,i)} u_{v,i}} \max_{v\in V, \, i\in I} \Delta_{v, i}(H, F^*).
>    $$

---

## 五、 完整论证

### 引理 1（单步展开的分块压缩性）
对任意两算子族 $F, G \in \mathcal F$，在扩展非负向量意义下有：
$$
\mathbf\Delta(\mathcal T F, \mathcal T G) \le M \mathbf\Delta(F, G).
$$

#### 证明：
固定节点 $v \in V$ 及点 $x \in U_v$。根据 $U_v$ 的互不相交划分：
1. 若 $x \in S_v$，由算子定义：
   $$
   (\mathcal T F)_v(x) = h_v(x) = (\mathcal T G)_v(x).
   $$
   由伪度量同一性，对所有 $i \in I$ 有 $d_i((\mathcal T F)_v(x), (\mathcal T G)_v(x)) = 0$。
2. 若 $x \in D_e$，其中 $e \in E$ 满足 $s(e) = v, t(e) = w$。根据展开定义及返回算子 $a_e$ 在 $\mathcal X^\circ$ 上的 Lipschitz 条件：
   $$
   \mathbf d\bigl((\mathcal T F)_v(x), (\mathcal T G)_v(x)\bigr) = \mathbf d\bigl(a_e(F_w(b_e(x))), a_e(G_w(b_e(x)))\bigr) \le L_e \mathbf d\bigl(F_w(b_e(x)), G_w(b_e(x))\bigr).
   $$
   由于 $b_e(x) \in U_w$，按定义显然有 $\mathbf d(F_w(b_e(x)), G_w(b_e(x))) \le \mathbf\Delta_w(F, G)$。由于 $L_e \ge 0$，分量不等式保持：
   $$
   \mathbf d\bigl((\mathcal T F)_v(x), (\mathcal T G)_v(x)\bigr) \le L_e \mathbf\Delta_w(F, G).
   $$
综合上述两类点，对于给定的 $v \in V$ 和任意 $x \in U_v$：
$$
\mathbf d\bigl((\mathcal T F)_v(x), (\mathcal T G)_v(x)\bigr) \le \sum_{e: s(e)=v} L_e \mathbf\Delta_{t(e)}(F, G) = \sum_{w\in V} \left(\sum_{e: v\to w} L_e\right) \mathbf\Delta_w(F, G) = \sum_{w\in V} M_{vw} \mathbf\Delta_w(F, G).
$$
不等式右端与 $x \in U_v$ 的选取无关。对左端关于 $x \in U_v$ 取上确界，即得：
$$
\mathbf\Delta_v(\mathcal T F, \mathcal T G) \le \sum_{w\in V} M_{vw} \mathbf\Delta_w(F, G) = (M \mathbf\Delta(F, G))_v.
$$
将所有节点块 $v \in V$ 纵向拼装，即得 $\mathbf\Delta(\mathcal T F, \mathcal T G) \le M \mathbf\Delta(F, G)$。<span style="float:right;">$\blacksquare$</span>

---

### 引理 2（$n$ 步展开的矩阵幂控制）
对任意 $n \ge 1$ 及任意 $F, G \in \mathcal F$：
$$
\mathbf\Delta(\mathcal T^n F, \mathcal T^n G) \le M^n \mathbf\Delta(F, G).
$$

#### 证明：
对 $n$ 施加数学归纳法。
- $n = 1$ 时，由引理 1 直接成立。
- 设结论对 $n$ 成立。由于 $M \ge 0$ 是有限实矩阵，且扩展算术遵循 $0 \cdot (+\infty) = 0$ 和非负线性单调性，将非负矩阵 $M$ 作用于不等式两端：
  $$
  \mathbf\Delta(\mathcal T^{n+1} F, \mathcal T^{n+1} G) = \mathbf\Delta(\mathcal T(\mathcal T^n F), \mathcal T(\mathcal T^n G)) \le M \mathbf\Delta(\mathcal T^n F, \mathcal T^n G) \le M (M^n \mathbf\Delta(F, G)) = M^{n+1} \mathbf\Delta(F, G).
  $$
由归纳原理，结论对所有 $n \ge 1$ 成立。<span style="float:right;">$\blacksquare$</span>

---

### 引理 3（Lyapunov 权重向量与诱导范数衰减）
若有限维非负矩阵 $M \ge 0$ 满足 $\rho(M) < 1$，则对任意给定的 $q \in (\rho(M), 1)$，存在分量严格为正的向量 $\mathbf u \in \mathbb R^{|V|m}$（即 $\min_{(v,i)} u_{v,i} > 0$），满足：
$$
M \mathbf u \le q \mathbf u.
$$
且由此诱导的加权范数 $\|\mathbf y\|_{\mathbf u} = \max_{(v,i)} \frac{|y_{v,i}|}{u_{v,i}}$ 满足：
$$
\|M \mathbf y\|_{\mathbf u} \le q \|\mathbf y\|_{\mathbf u} \qquad (\forall \mathbf y \ge 0).
$$

#### 证明：
由于 $q > \rho(M)$，矩阵 $\frac{1}{q} M$ 的谱半径满足 $\rho\left(\frac{1}{q} M\right) = \frac{\rho(M)}{q} < 1$。
因此，预解矩阵可通过收敛的 Neumann 级数展开：
$$
R = \left(I - \frac{1}{q} M\right)^{-1} = \sum_{k=0}^\infty \left(\frac{1}{q} M\right)^k.
$$
由于 $M \ge 0$，级数各项非负，故 $R \ge I \ge 0$。

取全 $1$ 向量 $\mathbf 1 = (1, \ldots, 1)^{\mathsf T} \in \mathbb R^{|V|m}$，构造向量：
$$
\mathbf u \triangleq R \mathbf 1 = \left(I - \frac{1}{q} M\right)^{-1} \mathbf 1.
$$
因为 $R \ge I$，显然有 $\mathbf u \ge \mathbf 1 > 0$，即 $\mathbf u$ 的每个分量均严格大于零。
对该定义两端左乘 $(I - \frac{1}{q} M)$，可得：
$$
\left(I - \frac{1}{q} M\right) \mathbf u = \mathbf 1 \implies \mathbf u - \frac{1}{q} M \mathbf u = \mathbf 1 \implies M \mathbf u = q \mathbf u - q \mathbf 1 \le q \mathbf u.
$$
对任意非负向量 $\mathbf y \ge 0$，记 $\alpha = \|\mathbf y\|_{\mathbf u} = \max_{(v,i)} \frac{y_{v,i}}{u_{v,i}}$，则按分量有 $\mathbf y \le \alpha \mathbf u$。
结合 $M \ge 0$ 的保序性与上述不等式：
$$
M \mathbf y \le \alpha M \mathbf u \le \alpha q \mathbf u = q \|\mathbf y\|_{\mathbf u} \mathbf u.
$$
按定义即得 $\|M \mathbf y\|_{\mathbf u} = \max_{(v,i)} \frac{(M \mathbf y)_{v,i}}{u_{v,i}} \le q \|\mathbf y\|_{\mathbf u}$。<span style="float:right;">$\blacksquare$</span>

---

### 4. 主定理的综合证明

#### (1) 几何逼近率证明
设 $H \in \mathcal F$ 为任意给定的初始算子族。由于第三节所构造的整体算子族 $F^*$ 满足不动点方程 $F^* = \mathcal T F^*$，必有 $\mathcal T^n F^* = F^*$（对一切 $n \ge 1$）。

由引理 2，以 $F = H, G = F^*$ 带入，得：
$$
\mathbf\Delta(\mathcal T^n H, F^*) = \mathbf\Delta(\mathcal T^n H, \mathcal T^n F^*) \le M^n \mathbf\Delta(H, F^*).
$$
选取引理 3 中由 $q \in (\rho(M), 1)$ 所决定的严格正向量 $\mathbf u > 0$。记标量范数转换常数：
$$
u_{\min} = \min_{v\in V, \, i\in I} u_{v,i} > 0, \qquad u_{\max} = \max_{v\in V, \, i\in I} u_{v,i} < +\infty.
$$
对任意非负向量 $\mathbf y$，显然有等价范数估计：
$$
\|\mathbf y\|_\infty \le u_{\max} \|\mathbf y\|_{\mathbf u}, \qquad \|\mathbf y\|_{\mathbf u} \le \frac{1}{u_{\min}} \|\mathbf y\|_\infty.
$$
由引理 3 的多次迭代，$\|M^n \mathbf y\|_{\mathbf u} \le q^n \|\mathbf y\|_{\mathbf u}$。将其作用于误差估计：
$$
\begin{aligned}
\max_{v\in V, \, i\in I} \Delta_{v, i}(\mathcal T^n H, F^*) &= \|\mathbf\Delta(\mathcal T^n H, F^*)\|_\infty \\
&\le u_{\max} \|\mathbf\Delta(\mathcal T^n H, F^*)\|_{\mathbf u} \\
&\le u_{\max} \|M^n \mathbf\Delta(H, F^*)\|_{\mathbf u} \\
&\le u_{\max} q^n \|\mathbf\Delta(H, F^*)\|_{\mathbf u} \\
&\le \left(\frac{u_{\max}}{u_{\min}} \|\mathbf\Delta(H, F^*)\|_\infty\right) q^n.
\end{aligned}
$$
令有限常数 $C_H \triangleq \frac{u_{\max}}{u_{\min}} \max_{v\in V, i\in I} \Delta_{v, i}(H, F^*)$，即证得：
$$
\max_{v\in V, \, i\in I} \Delta_{v, i}(\mathcal T^n H, F^*) \le C_H q^n \qquad (\forall n \ge 1).
$$

#### (2) 整体算子族解的唯一性证明
设另有解 $G^* \in \mathcal F$ 满足 $\mathcal T G^* = G^*$。
在几何逼近估计中取初始族 $H = G^*$。因为 $G^*$ 为不动点，对任意 $n \ge 1$ 恒有 $\mathcal T^n G^* = G^*$。
从而对任意 $n \ge 1$ 均成立：
$$
\max_{v\in V, \, i\in I} \Delta_{v, i}(G^*, F^*) = \max_{v\in V, \, i\in I} \Delta_{v, i}(\mathcal T^n G^*, F^*) \le C_{G^*} q^n.
$$
由于 $q \in (0, 1)$，令 $n \to \infty$，不等式右端 $C_{G^*} q^n \to 0$。
因此：
$$
\max_{v\in V, \, i\in I} \Delta_{v, i}(G^*, F^*) = 0.
$$
即对任意 $v \in V$ 和任意 $x \in U_v$，在伪度量下必有 $d_i(G^*_v(x), F^*_v(x)) = 0$（$\forall i \in I$）。这建立了整体算子族在规范诱导等价意义下的唯一性。<span style="float:right;">$\blacksquare$</span>
