# 复形记录的稳定消元

给定复 Hilbert 空间的有限长复形

$$0\longrightarrow H_0\xrightarrow{d_0}H_1\xrightarrow{d_1}\cdots\xrightarrow{d_{r-1}}H_r\longrightarrow0,$$

其中 $r\ge1$，每个 $d_j$ 是有界线性算子，$d_{j+1}d_j=0$。记 $H_{-1}=H_{r+1}=0$、$d_{-1}=d_r=0$。每一层的残留记录空间为

$$R_j=\ker d_j\big/\overline{d_{j-1}(H_{j-1})},$$

闭包取 Hilbert 范数闭包。已知所有 $R_j=0$。令

$$L_j=d_{j-1}d_{j-1}^*+d_j^*d_j:H_j\to H_j.$$

为这套复形建立稳定消元理论。目标是从给定数据构造有界线性算子 $s_j:H_j\to H_{j-1}$，使

$$d_{j-1}s_j+s_{j+1}d_j=I_{H_j}\qquad(0\le j\le r),$$

其中 $s_0=s_{r+1}=0$。同时为各 $L_j$ 构造有界线性右逆，并给出所得算子的范数控制。请给出主定理、构造及完整论证。
