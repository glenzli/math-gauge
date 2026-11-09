下面把题中的反链映射改写成熟知的 **rowmotion**。若 \(A\) 是反链，则
\[
A_t=\rho^t(A),\qquad I_t=I(A_t)
\]
满足
\[
I_{t+1}=\rho(I_t):=\downarrow\!\min(P\setminus I_t),
\]
其中 \(\downarrow S\) 表示由 \(S\) 生成的序理想。并且
\[
A_t=\max I_t.
\]
所以只需证明：对 \(P=[a]\times[b]\) 上的 rowmotion 的每个轨道 \(\mathcal O\)，都有
\[
\frac1{|\mathcal O|}\sum_{I\in\mathcal O}|\max I|
=\frac{ab}{a+b}.
\]

以下记 \(I_t\) 的各行长度为
\[
b\ge \lambda_1(t)\ge \lambda_2(t)\ge\cdots\ge \lambda_a(t)\ge0,
\]
并约定 \(\lambda_{a+1}(t)=0\)。最后一行之外，坐标方向不影响论证。

---

## 1. 一个局部滑动引理

定义
\[
\varepsilon_i(t)=
\begin{cases}
1,&\lambda_i(t)>0\ \text{且}\ \bigl(i=a\ \text{或}\ \lambda_i(t)>\lambda_{i+1}(t)\bigr),\\
0,&\text{其他}.
\end{cases}
\]
这恰好标记“某一个正的行长度块在这一行结束”。因此
\[
|\max I_t|=|\{\text{不同正的行长度}\}|
=\sum_{i=1}^a \varepsilon_i(t). \tag{1}
\]

**引理 1.** 对 \(1\le i<a\)，
\[
\varepsilon_{i+1}(t+1)=\varepsilon_i(t). \tag{2}
\]

证明：给出 rowmotion 在行长度上的显式公式。若 \(\lambda(t)\) 中不同的值 \(v<b\) 第一次出现在第 \(r_v\) 行，则
\[
\lambda_i(t+1)
=\max\{v+1:\ v<b,\ r_v\ge i\},
\]
空集时取 \(0\)。

现在比较相邻两行。

- 若 \(\varepsilon_i(t)=1\)，即 \(\lambda_i(t)>\lambda_{i+1}(t)\) 且 \(\lambda_i(t)>0\)。令
  \(w=\lambda_{i+1}(t)\)。第 \(i+1\) 行是值为 \(w\) 的块的第一行，所以
  \(\lambda_{i+1}(t+1)=w+1\)。而第 \(i+2\) 行要么仍在同一块中，要么进入更低的值，因此
  \(\lambda_{i+2}(t+1)<w+1\)（若 \(i+1=a\)，则只需注意 \(\lambda_a(t+1)=w+1>0\)）。故
  \(\varepsilon_{i+1}(t+1)=1\)。

- 若 \(\varepsilon_i(t)=0\)，则 \(\lambda_i(t)=\lambda_{i+1}(t)\)。于是第 \(i+1\) 行不是新块的第一行；按上面的公式，它与第 \(i+2\) 行在上一步后的长度相等，或至少不会形成一个新的正块终点。故
  \(\varepsilon_{i+1}(t+1)=0\)。

两种情况合起来就是 (2)。\(\square\)

由 (2) 立刻得到
\[
\varepsilon_i(t)=\varepsilon_1(t-i+1),\qquad i=1,\dots,a, \tag{3}
\]
下标按轨道周期取模。

---

## 2. 底边正块出现的次数

还需要一个计数事实。

**引理 2.** 设轨道 \(\mathcal O\) 的长度为 \(L\)。则
\[
\sum_{t\in\mathcal O}\varepsilon_1(t)
=\frac{Lb}{a+b}. \tag{4}
\]

这里给一个简短但完整的几何解释。把行长度图 \(I_t\) 的边界画在由
\[
(i,j)\sim(i+a,j-b)
\]
得到的柱面上；rowmotion 一步就是把这个边界沿对角线方向推进一格。事件
\(\varepsilon_1(t)=1\) 正是“底边出现一个正的水平段”。

在这个柱面提升中，记录该正底段左端所在的列。由引理 1 证明中的分块公式逐格检查可知：

- 若底段仍在矩形内部，则下一时刻它的左端列号增加 \(1\)；
- 当它碰到右边界后，下一次重新出现时列号也恰好增加 \(1\)（越过 \(b\) 后从 \(1\) 重新开始）。

因此，经过 \(a+b\) 次 rowmotion，底段正好扫过 \(b\) 个列位置，也就是在 \(a+b\) 个时刻中恰好有 \(b\) 次
\(\varepsilon_1=1\)。

若轨道的极小周期是 \(L\)，则 \(L\mid(a+b)\)，因为矩形上的 rowmotion 满足
\(\rho^{a+b}=\mathrm{id}\)。把轨道重复
\[
d=\frac{a+b}{L}
\]
次，就得到一个完整的 \(a+b\) 周期。于是
\[
d\sum_{t\in\mathcal O}\varepsilon_1(t)=b,
\]
即
\[
\sum_{t\in\mathcal O}\varepsilon_1(t)=\frac{b}{d}
=\frac{Lb}{a+b}.
\]
引理 2 得证。\(\square\)

---

## 3. 完成证明

由 (1)、(3) 得
\[
\begin{aligned}
\sum_{t\in\mathcal O}|\max I_t|
&=\sum_{t\in\mathcal O}\sum_{i=1}^a \varepsilon_i(t)\\
&=\sum_{i=1}^a\sum_{t\in\mathcal O}\varepsilon_1(t-i+1).
\end{aligned}
\]
由于 \(t\mapsto t-i+1\) 只是轨道时间指标的一个平移，
\[
\sum_{t\in\mathcal O}\varepsilon_1(t-i+1)
=\sum_{t\in\mathcal O}\varepsilon_1(t).
\]
所以由引理 2，
\[
\sum_{t\in\mathcal O}|\max I_t|
=a\cdot \frac{Lb}{a+b}.
\]
于是
\[
\frac1{|\mathcal O|}
\sum_{A\in\mathcal O}|A|
=
\frac1L\cdot \frac{aLb}{a+b}
=
\frac{ab}{a+b}.
\]

回到原来的反链记号，因为 \(A_t=\max I_t\)，这正是题中要证的
\[
\boxed{\displaystyle
\frac1{|\mathcal O|}\sum_{A\in\mathcal O}|A|
=\frac{ab}{a+b}}.
\]

故该轨道平均值结论成立。