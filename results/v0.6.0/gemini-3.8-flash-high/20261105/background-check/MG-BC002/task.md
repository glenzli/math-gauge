请独立解答以下题目。可使用本地工具进行计算、验证和保存自己的工作；不得访问网络或进行联网检索，也不得访问参考答案、评分、已有答卷或其他对话。

I am preparing the mathematical appendix and a short deployment description for an autonomous denoising block. The state is z=(x,y) in R², and

f(x,y) = (x²+2y²)/2 + (x+y)^4/4.

Write Φ_t(z) for the exact solution at time t of ż = −∇f(z), starting at z. Our block is T_τ=Φ_τ, with a configurable τ>0; stacking n identical blocks gives Z_n=T_τ^n(Z_0). This is the exact continuous-flow block, not an implicit-Euler discretization.

Here is the design rationale in the current draft: “The vector field is the gradient of a strongly convex energy, and its evolution is contractive and dissipative. Thus, for every τ>0, the exact block has a convex proximal representation T_τ=prox_{r_τ} for some proper lower-semicontinuous convex r_τ. This interpretation makes each deployed block an exact convex regularization step.” We use the convention

prox_r(z) = argmin_u {r(u) + ||u−z||²/2}.

Please supply the appendix and then a short deployment paragraph:

1. Establish forward global well-posedness, identify the equilibrium, and derive ||Φ_t(z)−Φ_t(w)||≤e^(−t)||z−w|| and f(Φ_t(z))≤e^(−2t)f(z). Deduce quantitative convergence for a stack.

2. State and prove the standard proximal certificate used in the rationale: if a map T admits T=prox_r with r proper, lower-semicontinuous and convex, then, for p=T(z) and every u in dom r,

r(p) + ||p−z||²/2 + ||u−p||²/2 ≤ r(u) + ||u−z||²/2.

Also derive firm nonexpansiveness under that representation.

3. Give a concise mathematical description of what the actual continuous-flow block and its repeated deployment guarantee, suitable for the methods section. Distinguish the evolution time τ from the coefficient in our definition of prox. A closed-form solution of the ODE is not needed.