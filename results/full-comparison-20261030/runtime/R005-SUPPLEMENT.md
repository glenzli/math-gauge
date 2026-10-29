# R005 新版单题补测入口

状态：只完成代码与合成测试。没有建立真实 session、运行预检请求或发送数学题。入口位于本目录的 `r005_supplement.py`，不修改冻结的 `scripts/benchmark` 或共享 `math_gauge`。本次修改不需要重跑已通过的全库门禁。

入口从独立单题 catalog 选取 `MG-R005` `0.3.1`；catalog 的 suite 可以是含 20 题的 `cases/public`。为了匹配共享 Suite 指纹，证据快照保存该 suite 的全部显式工件，但只对 R005 调用共享 `execution.run`。不会创建新 draft 题集或复制 runner 实现。请求顺序为 Terra/max 后 Gemini Flash/high，各一次；每阶段实际并发 1，上限仍为原 2。候选超时 2700 秒，外层共享 runner 留 90 秒退出余量。

运行前由 root 完成：

1. 首轮全部运行和评分结束，白名单归档、82 条完整性检查通过；保存最终 comparison，并成功离线复算。
2. 正式 R005 提升为 0.3.1，public suite 为 0.4.1；原轮旧材料和成绩继续保存在原 archive。数学、题文/Lean 对应和作者 Lean 证据通过后，更新当前 41 题 catalog，另建只选 R005 的补测 catalog。
3. 在全新的 `/private/tmp/math-gauge-r005-clarified-20261030` 中完成 CLI 身份、当前型号清单、预检。复用既有 preflight/isolation 函数及同样配置；只把固定 AGY 二进制路径移到新私有目录。模型/effort、CLI 版本和字节散列、拒读根、认证链接、读例外和负 probe 不得静默改变。新代理证据必须属于新根；只有原有 Terra 127.0.0.1:7897 例外。原凭据不读取、不修改。
4. 预检产出新根的 `config/{terra,gemini}.json`、身份/清单及 `preflight/qualification.json`，其中 mathematical_requests 必须为 0。qualification 的 bindings 必须包括两份新配置、两份新身份、两份新型号清单。原四份通过的搜索开/关能力控制显式继承，`control-reuse.json` 逐文件绑定原始事件、策略和账本；新 qualification 写明 0 次新非数学推理，不再运行四个 canary。

单题 catalog 沿用 `math-gauge.exercise-catalog/v1`，`snapshot_status` 为 `final-catalog-snapshot`，只含一条 suite row 和一条 case entry。suite row 的 cases 必须为 `["MG-R005"]`；row/entry 的 `suite_sha256` 均为共享 `Suite.load` 指纹。entry 需要 `case_id/version/task_kind/family_id/section/author_lean_coverage`。禁止把此 catalog 或评审材料传给候选。

root 在新根单独写 adoption gate，绑定首轮归档和复算，不复用首轮 release：

```json
{
  "schema": "math-gauge.supplement-adoption/v1",
  "released_by": "/root",
  "allow_session_preparation": true,
  "case_id": "MG-R005",
  "version": "0.3.1",
  "catalog_sha256": "NEW_SINGLE_CASE_CATALOG_SHA256",
  "new_mathematical_review_passed": true,
  "new_author_lean_validation_passed": true,
  "archive_manifest": {"path": "ABSOLUTE_ORIGINAL_ARCHIVE_MANIFEST", "sha256": "SHA256"},
  "offline_verification": {"path": "ABSOLUTE_ORIGINAL_OFFLINE_VERIFICATION", "sha256": "SHA256"},
  "original_comparison": {"path": "ABSOLUTE_ORIGINAL_FINAL_COMPARISON", "sha256": "SHA256"}
}
```

入口核验归档每个文件、原 freeze 身份、82 题次完整性、首轮评分 complete、offline matched 及彼此散列；不把 gate 的布尔确认当作 AI 人工审批。新 session 各自重做实际文件打开、loopback 拒绝 probe，且不得有任何旧数学账本。失败准备保留证据并停下，不在同目录覆盖重试。

后续操作命令模板如下；当前不执行：

```sh
python3 -B results/full-comparison-20261030/runtime/r005_supplement.py inspect --catalog SINGLE_CASE_CATALOG
python3 -B results/full-comparison-20261030/runtime/r005_supplement.py prepare --root NEW_ROOT --catalog SINGLE_CASE_CATALOG --adoption-gate ROOT_ADOPTION_JSON
python3 -B results/full-comparison-20261030/runtime/r005_supplement.py finalize --root NEW_ROOT
```

`finalize` 调用既有共享薄调度器的 finalization，只生成新 freeze，不放行数学请求。root 检查后在 **新根 runtime/** 下写独立 release，字段沿用 `math-gauge.comparison-release/v1`：`released_by=/root`、`allow_mathematical_requests=true`、新 `freeze_sha256/catalog_sha256`、`model_order=[terra,gemini]`；另外必须有 `experiment=r005-clarified-supplement` 和 `planned_mathematical_requests=2`。之后才可启动：

```sh
python3 -B results/full-comparison-20261030/runtime/r005_supplement.py run --root NEW_ROOT --release NEW_ROOT/runtime/root-release.json
```

每题调用原 `cli_adapter.py`，双方消息由共享 `candidate_message` 得出，绑定同字节 request/message；独立 run_id 和 model_label 保留。每个阶段结束调用现有 `postprocess.audit_case` 核验原始事件、账本、输入次数、PID/probe、receipt 和响应散列。失败停下一模型，不重试或替换；缺执行证据时请求数为 null，只有确认未调用且空账本/无运行记录才记 0。过滤未作答若执行资格完整则保留其终端输出，交数学评分单列。

新 runtime 保存 progress、queue-status/final、model-runs 和逐模型 execution-audit。评分仍用共享 compare_models 和单题 case index；结果仅属于该 1 题补测，不并入首轮 41 题，不替换旧答卷/分数。补测专用 `supplement_archive.py` 与 `supplement_replay.py` 已实现下面的完整归档与复算流程；所有基数来自该 freeze，不调用首轮写死 41/82 的整体归档检查。

合成验证命令：

```sh
python3 -B -m unittest discover -s results/full-comparison-20261030/runtime -p 'test_*supplement*.py' -v
```

15 项通过，全部仅临时合成工件；子进程仅本地 Python 文本回显和离线重算，没有 CLI、网络或模型请求。合成政策/PID/能力控制证据均明确标识 synthetic，不是实际过程验证或模型成绩。测试覆盖删除模拟旧根后仅凭归档重建精确结果、评分/文件篡改拒绝、缺失计数为未知、排除 state/凭据/链接/未声明文件、新代理与继承能力证据的逐字节保留。


## 无新增 canary 的最小预检命令

以下命令仅供首轮归档、复算和正式修订完成后的 root 执行。`supplement_preflight.py` 没有调用模型生成的入口；inspect 只运行 CLI 版本/帮助并读取型号元数据，proxy 检查已授权的本机精确代理与 HTTPS，inventory 只运行关闭 stdin 的型号列表。Gemini 认证沿用既有临时链接机制，不读取凭据正文，结束删除链接。

```sh
python3 -B results/full-comparison-20261030/runtime/supplement_preflight.py inspect --root NEW_ROOT --archive ORIGINAL_EVIDENCE_FINAL --agy-source /private/tmp/math-gauge-full-comparison-20261030/identity/gemini-02-pinned/agy
python3 -B results/full-comparison-20261030/runtime/supplement_preflight.py proxy --root NEW_ROOT
python3 -B results/full-comparison-20261030/runtime/supplement_preflight.py inventory --root NEW_ROOT
python3 -B results/full-comparison-20261030/runtime/supplement_preflight.py qualify --root NEW_ROOT --archive ORIGINAL_EVIDENCE_FINAL
```

inspect 从归档读取原配置与 CLI 身份，将 AGY 精确字节固定复制到新根，校验版本和散列，配置只替换身份/固定二进制路径。已有固定 AGY 文件应在清理首轮临时目录前复制；归档有意不包含可执行二进制。任一型号/effort/CLI 字节不再匹配则停止，不自动换型号。inventory 保持原 Flash/high 选择，即使清单后来新增更高档位也只记录而不切换。

qualify 从传入的归档 manifest 定位四份原来通过的能力控制，核对执行散列、CLI、型号/effort 与是否观察到搜索。`control-reuse.json` 列出继承的原始文件及来源 manifest；qualification 标明 `non_math_requests=0`、`inherited_control_requests=4`。随后上述 prepare 才创建两份新数学 session，实际检查文件拒读和网络拒绝，绝不复制旧 state 或旧对话。

## 补测最终评分、归档和离线复算

先按原流程完成全部初审、争议复核与最终 adjudication，并将最终 `reviews.json` 写入每个标准 run 根。原始初审、二审和根裁定等补充记录先逐字节保存到 `NEW_RESULTS/reviews/`。在该目录写显式白名单 `archive-inputs.json`：

```json
{
  "schema": "math-gauge.supplement-review-manifest/v1",
  "all_reviews_included": true,
  "files": [
    {"path": "primary-terra.json", "sha256": "EXACT_FILE_SHA256"},
    {"path": "primary-gemini.json", "sha256": "EXACT_FILE_SHA256"},
    {"path": "adjudication.json", "sha256": "EXACT_FILE_SHA256"}
  ]
}
```

`files` 应列所有实际存在的评审来源，不要求示例中的名字或数量；路径相对于清单所在目录，禁止越界或符号链接。标准 run 的 `reviews.json` 和存在的 `summary.json` 总是另行归档，清单用于保留全部额外原始评审，不会重新评分。

```sh
python3 -B results/full-comparison-20261030/runtime/supplement_archive.py audit --root NEW_ROOT --output NEW_RESULTS/final-runtime-audit.json
python3 -B results/full-comparison-20261030/runtime/supplement_archive.py report --root NEW_ROOT --output NEW_RESULTS/comparison.json
python3 -B results/full-comparison-20261030/runtime/supplement_archive.py archive --root NEW_ROOT --comparison NEW_RESULTS/comparison.json --review-manifest NEW_RESULTS/reviews/archive-inputs.json --output NEW_RESULTS/evidence-final
python3 -B NEW_RESULTS/evidence-final/tools/supplement_replay.py --archive NEW_RESULTS/evidence-final --output NEW_RESULTS/offline-recomputed
```

归档显式保留新脚本、adoption/release/catalog/freeze、qualification、继承能力与新预检/proxy证据、全部标准请求/答案/record/receipt/run/reviews、冻结题集及共享源码、额外评审和最终 comparison。所有动态路径由本次 freeze、qualification 或显式清单提供，没有固定首轮 preflight 目录。state、凭据、二进制、链接和未声明文件被排除；冻结 AGY state settings 仅通过同散列的 `runtime/task-settings.json` 保存副本及映射，不读取或复制 state。

归档先重新核验逐题身份、全部散列、请求次数、工具/PID/probe 与阶段顺序，并核对比较报告确由现有 run/reviews/receipt 产生；证据不足或报告过时会报错且保持原工件不变。缺失证据在 audit 中为 unknown，不能补成零。输出目录必须全新，禁止覆盖旧证据。若运行出现未解决的证据错误，应保留临时根和 audit，先解决归档资格，不能清理原根。

归档内的 `tools/supplement_replay.py` 可在原临时根删除后直接运行。它逐文件验证 manifest，只加载归档中保存的 shared compare_models，通过内存路径映射重定位 run/receipt；禁止打开旧临时根、联网和启动子进程。逐项比较 summary、groups、paired 与去除 run_dir 的 cases，并核对整份报告只忽略 created_at/run_dir 后一致。补测 R005 为 written，无候选 Lean 报告或编译义务；作者 Lean 证据已随冻结 suite 保存。原答案、评分、receipt 和 suite 字节不被改写。
