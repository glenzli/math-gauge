# 独立开放研究 1.3.0｜外部 harness 操作包

**仅交操作者。严禁把整个 ZIP、解包目录、`control-inputs/` 或运行证据交给考生。** R2 和 R3 的未发放题面在操作者侧。Only give the solver the files released for the current round.

这是同一道题的固定三轮。首轮交付冻结后发第二轮，第二轮冻结后发第三轮。全程用一个全新的独立求解会话，在同一会话中承接三轮。不给评分、暗示或其他反馈。三轮后停止。

## 开考前

- 用 Python 3.10 或更新版本，从操作者专用目录解包。`research_handoff.py` 只用标准库，负责离线复制、冻结和核对。原生 harness 负责实际出题、权限、计时和采集。
- 探测并建立独立文件及网络权限。候选端只挂载本轮获准材料、同一会话此前自己的内容和可写临时工作区。可用当地工具和预装公共依赖，禁用联网检索、工具联网、其他会话、项目与操作者资料。模型服务和登录流量单独记录。禁止把 bundle、候选工作区之外的捕获目录或 state 挂给候选。目录分离、题面禁令及 `session-id` 声明本身不能证明系统隔离或会话真实新建。
- 每轮 2700 秒，从实际下发开始。设定 controller／broker 的 2700 秒有效截止，并分别记录 native 时限、输出上限与 CLI／外层清理预算。首个原生终态或截止，以先到者为截点，立即停止候选写入。CLI 清理可以晚于截点。实际权限、预算、时钟及未知项按 harness 留证。
- `--metadata` 可绑定一份操作者 JSON 原件。建议记录 harness 及版本、请求模型和推理设置、可观察后端、实际权限和探针、会话建立方式、各层时限与未知原因。只保存可回交的证据，勿写入认证凭据。未提供的字段保持未知。

## 逐轮发放

下面命令在操作者解包目录执行。`STATE` 是尚不存在的私有目录，`SESSION` 是在实际全新求解会话中确认的标识，`R1_INPUT` 等是彼此分开的新发放目录，`CAPTURE` 是每轮一个新建的操作者侧采集目录。它们不能位于解包目录内。若路径有符号链接，请用实际物理路径。一次只操作一个轮次。

```sh
python3 research_handoff.py check
python3 research_handoff.py prepare --state "$STATE" --session-id "$SESSION" --metadata "$METADATA"
python3 research_handoff.py reveal --state "$STATE" --session-id "$SESSION" --round R1 --output "$R1_INPUT"
```

R1 只发放 `task.md`、`rules.md`、`packet/body.md` 及 `packet/figures/` 下的四图。保持相对路径。将 `rules.md` 作为该会话的长期规则，原样发送 `task.md` 和附件。冻结 R1 后用同一条 `reveal` 命令改成 R2 和新的输出目录；冻结 R2 后同样发 R3。R2 和 R3 的新发放目录只含本轮 `task.md`，固定正文、图和规则仍是首轮所给版本。每轮保留实际发送的内容及传输方式。

## 逐轮封卷和回交

按实际原生记录收集首个正常用户可见 final 的完整字节。保存最终响应原件，不补标题、不摘取证明、不改变编码和换行。生成结束与 CLI 退出分别留证；单独的 DONE、可读 ERROR、流式片段或本地未交稿件不构成正常交卷。

停止候选写入后，用本轮真实观察填 `observation.json`。工具可生成空白模板：

```sh
python3 research_handoff.py observation-template --session-id "$SESSION" --round R1 \
  --output "$CAPTURE/observation.json"
```

- `request_id` 是本轮唯一实际请求标识。用带时区的 ISO 8601 时间填写 `dispatched_at`、`boundary.at` 和可证实的 `first_normal_final_at`。原生终态的 `status` 留原标签，`classification` 用 `success`、`failure` 或 `unknown`，`at` 记录实际时刻。`cli_cleanup` 单列 `exit_code` 和 `at`，缺资料可填 `null`。
- 正常交卷用 `delivery: "normal-final"`、`first_normal_final: true` 和 `final: "native-final.md"`，文件放在 `CAPTURE` 中。可获取原生终态时，`boundary.kind` 用 `native-terminal`，`boundary.at` 与成功终态时刻一致，final 必须在此之前或同时且不晚于时限。若界面能正面确认首个正常 final 及其时间，但终态接口不可得，`native_terminal` 留 `null`，`boundary.kind` 用 `first-normal-final`，`boundary.at` 等于该 final 的时间，`evidence_gaps` 说明缺什么。这样的记录仍是操作者声明。
- `attachments` 只列该 final 明确交付的相对 Markdown 路径。`--candidate-files` 指向候选的已停止写入输出树，不要指向获准输入目录。未明确交付的工作文件不得列入。保留不可用附件的原文和原因，勿补造替代。`evidence_files` 可列 `CAPTURE` 下独立保留的原始请求、事件流、原生状态、运行或权限证据，不采集目录中的其余文件。路径不可绝对、越界或经链接。
- 已确认截止未交卷或已确认的其他交付失败，用 `delivery-failed` 及实际 `deadline`／`native-terminal` 边界。截止时刻为本轮下发加 2700 秒，之后的原生终态另列。归因或边界不确定，用 `unresolved`，不可把已知缺口补为成功。两者的 `first_normal_final`、`first_normal_final_at`、`final` 均为 `null`，`attachments` 为空，可保留原生运行证据。后续轮自动受阻。此流程不会自动重试或评审。

```sh
python3 research_handoff.py freeze --state "$STATE" --session-id "$SESSION" --round R1 \
  --capture "$CAPTURE" --candidate-files "$STOPPED_OUTPUT"
python3 research_handoff.py check --state "$STATE"
```

无附件时可省略 `--candidate-files`。封卷通过后才运行下一轮的 `reveal`。每轮状态记录原始声明、首份正常原稿、显式附件、列明的原始运行证据以及 SHA-256。`R<n>/seal.json` 绑定本轮发放记录和前一轮封卷。冻结后的源文件不可覆盖。若写入异常中断，保留所有已写原件、目录和运行记录，停止继续发放并请评审方核对。`--fixture` 仅用于合成验证，用于 `prepare` 和模板，不能与真实回交混用。

最后留存完整 `STATE`、`check` 输出中的最终封印 SHA-256、实际发送的输入记录、执行环境证据、每个物理请求（含失败／未决）及其原件，通过获准的私有路径交回评审。`check` 验证已复制字节、声明结构和发放／封卷顺序。平台身份、真实沙箱、实际下发与截止、首份 final 的来源及数学正确性仍需独立核验。回交记录不自动成为榜单成绩。
