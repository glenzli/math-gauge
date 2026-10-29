# 来源与抽取边界

## 已核实的原始对应

- [Voevodsky，Cohomological theory of presheaves with transfers](https://www.math.ias.edu/Voevodsky/files/files-original/Dropbox/Published_papers/Motives/Collection/s3.pdf)：原 PDF 印刷页 34（PDF 第 34 页）的命题 4.23 声称每个二开覆盖上的短列正合；随后命题 4.24 给出半局部值与 Zariski 层化值相同这一应用。本次已读取相关完整段落。
- [Mazza–Voevodsky–Weibel，Lecture notes on motivic cohomology](https://sites.math.rutgers.edu/~weibel/MVWnotes/prova-hyperlink.pdf)：命题 11.1（印刷页 83）；引理 22.9、22.10（185–186）；推论 22.11、引理 22.12（186–187）。引理 22.10 后明确把更正定位到原 4.23：原证明遗漏了从 $U_0$ 到 $U$ 的收缩。候选主目标对应 22.12；参考证明使用的是更正后的 22.10。
- [Weibel 的作者说明页](https://sites.math.rutgers.edu/~weibel/motiviclectures.html)把该链接描述为 2005 年 12 月最终讲义版本，并说明书于 2006 年出版。此次实际下载的 PDF 为 228 页；不把网站的“230 页”描述当作文件身份。
- [Voevodsky 的 2014 年本人回顾](https://www.ias.edu/ideas/2014/voevodsky-origins)提供发现错误和以较弱引理修复应用的历史背景；技术对应以两个数学原文为准。

所有来源均公开；访问日期为 2026-10-29。本题不使用未公开 OET、私有论文或真实候选答卷。

## 文件固定

source-evidence.json 记录下载 URL、字节数与 SHA-256。临时工作副本不列为候选附件，也未把整本第三方文献复制进本题。复核者可重新下载并比较散列；页码以固定文件为准。

原论文 SHA-256：`661f974601f02e83b80c957e673053d1cd62d6f26315ac48db06b8c52b038029`。

修正版讲义 SHA-256：`bb07651d8cc1b38f2552204e6c777cc7570c19e35d779987907a44efc2669486`。

作者页所链的勘误 PDF，以及相同路径的 sites.math.rutgers.edu 版本，本次均返回 404。本稿不以此推断不存在其他勘误。

## 保留、改编与未覆盖部分

保留实际几何对象、任意底域、同伦不变带转移预层、任意有限点集、半局部邻域余极限，以及典范层化比较同构。题面独立用中文整理；不展示历史错误或收缩路线。

参考论证把原先的极限与图追论证展开，并选用闭点集合的互不相交划分：一个邻域明确排除第一闭点，因而修正版收缩仍必须保留该闭点。这用于核实收缩后的开集对仍位于同一邻域系统，未加强原题假设。

这不是一项新定理，也不是仅凭回顾文章杜撰的类比。本稿引用精确的已知几何输入，没有重建标准三元组、相对 Picard 群、有限底域转移或链同伦的完整几何证明。未给出原错误命题的具体几何反例；reference.md 的乘 $2$ 余极限例子是独立的阿贝尔群说明，不能移作该反例。

直接适用已知主定理是合法短解。公开来源使检索与训练污染具有现实可能；未据历史复杂性推断现代模型难度，未运行候选模型。
