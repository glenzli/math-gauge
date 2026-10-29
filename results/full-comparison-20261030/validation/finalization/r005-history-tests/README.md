# R005 修订后的研究题集测试适配

本次仅编辑 `tests/test_research_suite.py`，保留接手时已有的二十题扩展测试。未编辑题面、当前 catalog、报告、生产 runner 或 Lean 源码。

变更：

- 当前题集版本断言改为 public 0.4.1；R005 为 0.3.1，原十题中的其余九题仍为 0.3.0，新增十题仍为 0.4.0。
- 从原十题的 suite.json / sources.json 重建临时基线。R005 的旧文件位置由当前 revision.json 的 historical_snapshot 指定，先核对快照散列、题号和旧版本，再按原目录布局挂入其 0.3.0 文件。其余九题使用当前源字节。
- 使用共享 Suite.load / Suite.request 验证原十题完整 suite SHA、每个既有文件的字节数与 SHA，以及全部旧请求散列。没有把旧版预期改成新版散列。
- 新增明确的 R005 当前版本与 task-only 输入检查，要求当前请求只在版本和题面上区别于历史请求；题面匹配 revision 记录的精确 SHA。
- 新增混版回归：只在临时重建目录把新版 task 放入旧版 case，要求其 suite SHA 和 request SHA 均不能复用旧基线身份。冻结题目目录不参与测试写入。

验证命令：

`python3 -m unittest discover -s tests -p test_research_suite.py -v`

结果：7 tests passed。Python 语法解析与 scoped `git diff --check` 通过。完整逐项输出见 `focused-tests.log`，源文件和日志散列见 `validation.json`。

当前 public suite SHA 仍为 `6ad8a8a7c80a7ba769b0677ef250bf9998d9601d190f271ce6b357fa91f5308d`，与补测冻结值相同。全库测试由 root 在其 review.py 变更后统一运行，本任务不重复广泛测试。不 commit / push。
