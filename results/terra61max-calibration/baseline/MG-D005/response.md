**总能得到偏序集，包括 \(X=\varnothing\) 的情形。**

先证 \(\sim\) 为等价关系。自反性由 \(x\le x\) 得到；对称性由定义中两个方向的交换得到。若 \(x\sim y\)、\(y\sim z\)，则由传递性有 \(x\le y\le z\) 和 \(z\le y\le x\)，所以 \(x\sim z\)。

再证代表元无关。若 \(x'\sim x\)、\(y'\sim y\) 且 \(x\le y\)，则
\[
x'\le x\le y\le y',
\]
故 \(x'\le y'\)。交换新旧代表元也得逆向蕴含，所以 \([x]\preceq[y]\) 的真假不依赖选择。

最后，\([x]\preceq[x]\) 来自原关系自反性；若 \([x]\preceq[y]\preceq[z]\)，则 \(x\le y\le z\)，故 \([x]\preceq[z]\)。若 \([x]\preceq[y]\) 且 \([y]\preceq[x]\)，则 \(x\sim y\)，所以 \([x]=[y]\)，即商关系反对称。等价类相等与元素等价互相等价，故该步骤有效。

\(X=\varnothing\) 时商集为空，三个偏序公理都无反例地成立。证明不要求原关系反对称或 \(X\) 有限。