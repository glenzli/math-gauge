# 独立数学作答题包

各题互相独立。只使用每题给定材料，按题号分别给出完整作答。

## MGH-D001
使用题面实际给定的条件。区分已证明的结论、附加假设下的结果和未证猜想。给出可审核的论证。
# 子空间的内中心覆盖
令 (X,d) 为任意扩展伪度量空间，允许不同点零距以及距离为无穷；d 对称、自距为零且满足三角不等式。对 S⊆X 和实数 r>0，定义 N_S(r) 为用开球 {x∈S:d(x,s)<r} 覆盖 S 所需的最小有限球数，球心必须属于 S；若不存在有限覆盖则记为 ∞，约定 N_∅(r)=0。
1. 对所有 U⊆V⊆X，是否总有 N_U(r)≤N_V(r)？证明或给出完整反例。
2. 在常数 c∈[1,∞) 中，找出使 N_U(cr)≤N_V(r) 对上述所有空间、子集和有限正半径成立的最小常数，并证明成立性和最优性。不得默认覆盖球心属于 U、距离有限、分离性或任一集合非空。


## MGH-D002
使用题面实际给定的条件。区分已证明的结论、附加假设下的结果和未证猜想。给出可审核的论证。
# 非负系数证书有没有最小值
X、Y 为任意集合，U⊆X；d₁,d₂ 是 X 上的扩展伪度量，e 是 Y 上的扩展伪度量，f:X→Y。用题面约定 0·∞=∞·0=0，其余乘法为通常扩展非负数乘法。令
C={ (a,b)∈[0,∞]² : ∀x,y∈U, e(fx,fy)≤a d₁(x,y)+b d₂(x,y) }。
假定 C 非空。坐标序记为 ≤。M∈C 称为极小元，指不存在 K∈C 满足 K≤M 且 K≠M；最小元则必须小于等于 C 的每个元素。
逐项判定并证明或反驳：
A. (inf{a:(a,b)∈C}, inf{b:(a,b)∈C}) 总属于 C。
B. C 总有极小元。
C. 如果对每对 x,y∈U 两个输入距离都有限，而且指定的 L⁰∈C 两个坐标都有限，那么存在极小元 M∈C，满足 M≤L⁰。这里没有对全体输入距离给出统一有界性，也不假定 U 有限或 e 的所有距离有限。
反例必须实现为满足所列公理的实际距离与映射，不能只凭空指定系数集合。


## MGH-F001
使用题面实际给定的条件。区分已证明的结论、附加假设下的结果和未证猜想。给出可审核的论证。
# 演化可兼容的观察细化
自然语言目标：给任意集合 X、自映射 f:X→X 以及等价关系 R，构造一个等价关系 E，使 E⊆R、x E y 蕴含 f(x) E f(y)，并且任何满足这两个性质的等价关系 S 都包含于 E。这里不假定 f 保持 R，不要求 X 有限或非空。
请审核附件 candidate.lean：实际类型、依赖和证明是否完整对应上述目标；说明定义中的迭代顺序和量词。区分代码自身的有效性与语义覆盖，不把新增假设下的修复说成原文件已完成。仅静态审核即可，Lean 4.29.1 标准库。

### 附件：candidate.lean
~~~~
import Std
namespace MGHF001
universe u
variable {α : Type u}
def step (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => step f n (f x)
def Stable (f : α → α) (S : α → α → Prop) : Prop :=
  ∀ x y, S x y → S (f x) (f y)
def Included (S R : α → α → Prop) : Prop := ∀ x y, S x y → R x y
def Trace (f : α → α) (R : α → α → Prop) (x y : α) : Prop :=
  ∀ n, R (step f n x) (step f n y)
theorem candidate (f : α → α) (R : α → α → Prop) (hR : Equivalence R) :
    ∃ E : α → α → Prop, Equivalence E ∧ Included E R ∧ Stable f E ∧
      (∀ S : α → α → Prop, Equivalence S → Included S R → Stable f S → Included S E) := by
  refine ⟨Trace f R, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro x n
      exact hR.refl (step f n x)
    · intro x y h n
      exact hR.symm (h n)
    · intro x y z hxy hyz n
      exact hR.trans (hxy n) (hyz n)
  · intro x y h
    exact h 0
  · intro x y h n
    exact h (n + 1)
  · intro S _hS hSR hSf x y hxy n
    apply hSR
    induction n generalizing x y with
    | zero => exact hxy
    | succ n ih => exact ih (f x) (f y) (hSf x y hxy)
#print axioms candidate
end MGHF001

~~~~

## MGH-F002
使用题面实际给定的条件。区分已证明的结论、附加假设下的结果和未证猜想。给出可审核的论证。
# 部分演化的商
给定任意 X、等价关系 E、子集 D⊆X 及总函数 f:X→X；只有 f|D 被视为实际演化。唯一的相容条件是：若 x,y∈D 且 x E y，则 f(x) E f(y)。
自然语言目标：在 Q=X/E 上构造部分函数 F，要求对每个 x∈X，F 在 [x] 处有定义当且仅当 x∈D；当 x∈D 时 F([x])=[f(x)]。
作者提交 candidate.lean，宣称已完成这个目标。请完整审核附件，说明其实际定义与定理、能建立的商对象，以及与自然语言目标的关系；若目标无法从前提推出，给出满足全部条件的反例，并明确需要怎样的修复。不要仅因为存在某种商上的部分函数就忽略上述逐代表元的定义域要求。Lean 4.29.1 标准库，仅需静态审核。

### 附件：candidate.lean
~~~~
import Std
namespace MGHF002
universe u
variable {α : Type u}
def ImageGraph (s : Setoid α) (D : α → Prop) (f : α → α)
    (q r : Quotient s) : Prop :=
  ∃ x : α, D x ∧ Quotient.mk s x = q ∧ Quotient.mk s (f x) = r
def RightUnique {β : Type u} (G : β → β → Prop) : Prop :=
  ∀ q r₁ r₂, G q r₁ → G q r₂ → r₁ = r₂
theorem candidate (s : Setoid α) (D : α → Prop) (f : α → α)
    (h : ∀ x y, D x → D y → s.r x y → s.r (f x) (f y)) :
    RightUnique (ImageGraph s D f) := by
  intro q r₁ r₂ hx hy
  obtain ⟨x, hDx, hxq, hxr⟩ := hx
  obtain ⟨y, hDy, hyq, hyr⟩ := hy
  have hxy : s.r x y := Quotient.exact (hxq.trans hyq.symm)
  have hout : Quotient.mk s (f x) = Quotient.mk s (f y) :=
    Quotient.sound (h x y hDx hDy hxy)
  exact hxr.symm.trans (hout.trans hyr)
#print axioms candidate
end MGHF002

~~~~

## MGH-E001
使用题面实际给定的条件。区分已证明的结论、附加假设下的结果和未证猜想。给出可审核的论证。
# 带观察的分支演化压缩
X 为任意集合，T⊆X×X 为任意一步演化关系，O 为 X 上的等价关系。一步演化可能不存在、只有一个或任意多个后继；不假定有限分支、确定性或有限状态。
希望合并观察上等价的状态，同时完整保留下一步可到达的商状态集合。具体地，一个允许的等价关系 E 必须包含于 O；若 x E y，则对每个满足 xTx' 的 x'，存在满足 yTy' 且 x' E y' 的 y'，反方向也成立。
在这些条件下研究可以怎样压缩：给出你能证明的存在性、构造、极值或普遍性质，说明商上的演化究竟保留什么。可以研究通过不断细化关系求解的过程，但不要默加有限分支或把有限层观察自动等同于全部行为。目标没有指定唯一结论；请完整证明实际声称的结果，并把未证方向分开。


## MGH-E002
使用题面实际给定的条件。区分已证明的结论、附加假设下的结果和未证猜想。给出可审核的论证。
# 允许无限前提的生成规则
X 为任意集合，A⊆X。规则集合 Γ⊆P(X)×X；一条 (B,x) 的含义是，当当前集合已经包含 B 的每个元素时，可以加入 x。B 可以为空、有限或无限，不假定 Γ 有限。
请研究由 A 生成的最小规则封闭集（“封闭”指每条规则 (B,x) 的 B⊆C 都蕴含 x∈C）：给出构造及你能证明的性质，分析实际规则逐步触发与该对象的关系，特别注意无限前提对构造步数和子集族极限的影响。允许把子集集合作为导出的辅助结构；不要假设 X 自带序、拓扑或完备性，也不要暗中把无限前提改为有限前提。
这是开放构造题，没有指定唯一结论或停止步数。请证明你的实际结果，区分一般结论、明确附加条件后的结论和未证猜想。

