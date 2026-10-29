这些文件在数学上给出了全序列上的线性逆，并证明它保持快速衰减。**提交结果缺少的是目标中的一阶估计声明**：现有估计要求输入满足 \(r+2\) 阶控制，而目标只要求 \(r+1\) 阶控制。目标估计本身是正确的，可以直接从已有定义补证。

**代码有效性。** 静态审查未发现明显的类型或证明错误，给出的源码也没有显式使用 `sorry` 或自定义公理。但当前执行工具不可用，我无法在指定的 Lean 和 Mathlib 版本中实际编译，也无法核验两条 `#print axioms` 的输出。因此，不能将编译通过或具体公理依赖当作已验证事实。`#print axioms` 即使运行成功，也只报告声明的公理依赖，不能判断其命题是否覆盖目标。

**已覆盖的结论。** 以 `solve` 为 \(S\)，`Multiplier.lean` 中的声明分别给出：

- `transport_solve` 和 `solve_transport`：\(T(Sf)=f\) 且 \(S(Tu)=u\)；`solution_unique` 也单独给出解的唯一性。
- `solve_add` 和 `solve_smul`：`solve` 对全部实序列满足加法和实数数乘律，因而是线性的。它没有被打包为 Lean 的 `LinearMap`，但数学上的线性已经由这两个定理表达。
- `rapid_solve`：快速衰减序列经 `solve` 后仍快速衰减。证明取输入的 \(r+2\) 阶控制是足够的，因为快速衰减对每一阶都提供控制。

这些结论由全局函数 `solve : Seq → Seq` 及其定理表达。相比之下，`candidate r C f h` 需要先提供控制证明 `h`；单独把 `candidate` 当作对外接口，不能对任意序列无条件调用。例如常数序列 \(f_n=1\) 不满足任何有限常数下的 `InputControl r C f`。

**未覆盖的估计。** `control_solve_buffered` 和 `candidate` 的实际前提是
\[
\operatorname{Control}(r+2,C,f),
\]
目标的前提则是 \(\operatorname{Control}(r+1,C,f)\)。前者严格更强。取 \(r=0\)、\(C=1\)，令 \(f_1=\tfrac12\)，其余项为零，则
\[
\operatorname{Control}(1,1,f)\quad\text{成立},\qquad
\operatorname{Control}(2,1,f)\quad\text{不成立}.
\]
这个 \(f\) 甚至快速衰减，因此快速衰减也不能补足指定常数 \(C=1\) 下的 `candidate` 前提。

另一方面，由 \(w_n>0\) 有逐点恒等式
\[
w_n^r |(Sf)_n|
=w_n^r |w_n f_n|
=w_n^{r+1}|f_n|.
\]
所以实际上对任意实数 \(C\)，两个控制条件等价：
\[
\operatorname{Control}(r,C,Sf)
\iff \operatorname{Control}(r+1,C,f).
\]
不需要额外假设 \(C\ge0\)；若 \(C<0\)，控制条件本身不可能成立。

可以在同一命名空间中加入下面的定理；它复用了现有证明中的逐点计算：

```lean
theorem control_solve {r : ℕ} {C : ℝ} {f : Seq}
    (h : Control (r + 1) C f) : Control r C (solve f) := by
  intro n
  calc
    weight n ^ r * |solve f n| =
        weight n ^ (r + 1) * |f n| := by
      rw [solve, abs_mul, abs_of_pos (weight_pos n), pow_succ]
      ring
    _ ≤ C := h n
```

随后将 `InputControl` 改为 `Control (r + 1) C f`，并将 `candidate` 的 `estimate` 改为 `control_solve h`，即可让该接口表达目标的同常数估计。上述补充代码同样尚未经过实际 Lean 编译验证。