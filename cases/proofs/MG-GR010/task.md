# 探针映射空间与连续性层级

版本 0.1.1。以下全部阶段均须作答。

采用ZFC，固定Grothendieck宇宙U∈V、N∈U，所有空间U小Hausdorff。Prof_U为紧全不连通空间范畴，h_X(S)=C(S,X)，限制为预复合。记H_X,Y(S)=Nat(h_S×h_X,h_Y)。C_co(X,Y)表示紧开拓扑的连续函数空间，子基[K,O]={f:f(K)⊂O}，K紧、O开。kX是在同一底集上的拓扑：O开当且仅当每个U小紧Hausdorff探针f:K→X都使f⁻¹O开。X紧生成指kX=X；X×_kY=k(X×Y)。

逐 S 编号交付。证明题须写出论证；判断题须明确结论并给证明或完整核验反例；构造题须验证所需性质。援引此前结果或标准定理时，说明其条件在当前阶段为何适用。各阶段的附加条件只在该阶段明确指定的范围内生效。未完成内容请明确标记。

## S1　局部紧输入

设X局部紧Hausdorff，Y,Z任意Hausdorff。证明通常求值C_co(X,Y)×X→Y连续，并证明C(Z,C_co(X,Y))≅C(Z×X,Y)的柯里化双射及其自然性。

## S2　探针能检测的映射

证明profinite探针与全部紧Hausdorff探针给出相同k拓扑，并证明Nat(h_X,h_Y)≅C(kX,kY)。进而证明：对固定X，所有Y的此类自然变换都由原拓扑连续X→Y诱导，当且仅当X紧生成。

## S3　全部参数化映射记录

对任意X,Y构造Hausdorff空间M(X,Y)，确定底集与拓扑，使C(S,M)≅H_X,Y(S)在全部profinite S上自然。构造ev:h_M×h_X→h_Y，证明对每个Hausdorff Z，α↦ev∘(α×I)给Nat(h_Z,h_M)≅Nat(h_Z×h_X,h_Y)，并验证X,Y中的连续映射自然性。

## S4　可数邻域基的输入

设X是第一可数Hausdorff空间，Y Hausdorff。判断通常求值C_co(X,Y)×X→Y是否必连续。同时说明第一可数性是否足以保证kX=X。

## S5　空间实现的识别

设f:X→Y连续，并且h_f:h_X→h_Y是自然同构。判断f是否必为原拓扑的同胚。

## S6　复合与可识别范围

对S3所构造的紧生成实现，构造连续复合M(Y,Z)×_kM(X,Y)→M(X,Z)，证明结合律与单位律。给连续f:X→Y满足h_f同构的充要条件，并判断X,Y第一可数时是否能升级为普通同胚。
