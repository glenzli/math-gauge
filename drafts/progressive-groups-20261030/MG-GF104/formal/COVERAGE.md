# MG-GF104 作者 Lean 覆盖

当前题面 0.1.1 的全部 6 阶段均有作者证明、反例或审计对应。机器核验与语义审核是不同证据；人工审核仍待完成，未运行候选模型。

定义和已证辅助声明从母题作者源显式收录；逐文件来源/原哈希/当前哈希见 alignment.json 的 attribution。新增声明不借用母题旧编译记录，全部源在当前 manifest 中重新绑定。

## S1

单个单射到离散空间；X可空。 任意U=f^-1(f(U))使诱导拓扑离散；原sInf可行拓扑构造总离散，恰在此特例正确。

声明：`Extensions.MathGauge.F104.induced_injective_discrete`, `Extensions.MathGauge.F104.singleton_discrete_initial`, `Boundary.MathGauge.F104.legacyAssembled_eq_bot`。

## S2

任意指标/源/目标族，所有测试域Z与s,g，含空族。 修复 assembled 为iInf induced；无单射、离散、T0或非空前提。

声明：`Candidate.MathGauge.F104.candidate_realizes`, `Candidate.MathGauge.F104.candidate_coarsest`, `Candidate.MathGauge.F104.candidate_inbound`, `Candidate.MathGauge.F104.candidate_unique`, `Extensions.MathGauge.F104.empty_family`。

## S3

任意E:Set X，包括空集；包含为Subtype.val。 induced_iInf与induced_compose给严格相等，无E开闭要求。

声明：`Extensions.MathGauge.F104.subspace_initial`。

## S4

每目标T0，∀x,y,(∀i,f_i x=f_i y)→x=y；指标可无限/空。 用标准T0Space及Inseparable连续像证明；限制族仍联合单射，任意E成立。空族强制Subsingleton X。

声明：`Extensions.MathGauge.F104.jointly_injective_t0`, `Extensions.MathGauge.F104.subspace_t0`, `Extensions.MathGauge.F104.empty_joint_subsingleton`。

## S5

Bool源、Unit唯一目标为T0，常值观测。 精确算τ=⊤且Bool非T0，同时证明联合单射条件失败。

声明：`Extensions.MathGauge.F104.top_bool_not_t0`, `Extensions.MathGauge.F104.t0_targets_counterexample`。

## S6

原错误构造由Legacy保存为legacyAssembled；修复仅修改作者侧Construction/Candidate。 证明原构造恒离散及完整映入逆向失败见证；不是把编译错误当数学反例。所有候选输入原件未动。

声明：`Boundary.MathGauge.F104.legacyAssembled_eq_bot`, `Boundary.MathGauge.F104.discrete_fails_coarsest`, `Boundary.MathGauge.F104.inbound_reverse_fails`, `Candidate.MathGauge.F104.candidate_realizes`, `Candidate.MathGauge.F104.candidate_coarsest`, `Candidate.MathGauge.F104.candidate_inbound`, `Candidate.MathGauge.F104.candidate_unique`, `Extensions.MathGauge.F104.subspace_initial`, `Extensions.MathGauge.F104.jointly_injective_t0`, `Extensions.MathGauge.F104.t0_targets_counterexample`。

编译入口及逐模块顺序由 manifest.json 明示；CurrentAudit.lean 遍历全部本地声明的传递公理闭包。正式证据为 verification-report.json、declarations.json 和 logs/，只承认与清单完全相同的源哈希。源码检查没有 sorry/admit/新增公理。
