/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Roots
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub0 (p : Pattern) : d0 (change p 10000 none) = d0 p := by
  rfl
theorem sub1 (p : Pattern) : d2 (change p 10000 none) = d2 p := by
  rfl
theorem sub2 (p : Pattern) : d6 (change p 10000 none) = d6 p := by
  change (if p 193 then d2 (change p 10000 none) else d0 (change p 10000 none)) = d6 p
  rw [sub1, sub0]
  rfl
theorem sub3 (p : Pattern) : d7 (change p 10000 none) = d7 p := by
  change (if p 192 then d6 (change p 10000 none) else d0 (change p 10000 none)) = d7 p
  rw [sub2, sub0]
  rfl
theorem sub4 (p : Pattern) : d4 (change p 10000 none) = d4 p := by
  rfl
theorem sub5 (p : Pattern) : d54 (change p 10000 none) = d54 p := by
  change (if p 193 then d4 (change p 10000 none) else d2 (change p 10000 none)) = d54 p
  rw [sub4, sub1]
  rfl
theorem sub6 (p : Pattern) : d55 (change p 10000 none) = d55 p := by
  change (if p 192 then d54 (change p 10000 none) else d2 (change p 10000 none)) = d55 p
  rw [sub5, sub1]
  rfl
theorem sub7 (p : Pattern) : d56 (change p 10000 none) = d56 p := by
  change (if p 186 then d55 (change p 10000 none) else d7 (change p 10000 none)) = d56 p
  rw [sub6, sub3]
  rfl
theorem sub8 (p : Pattern) : d57 (change p 10000 none) = d57 p := by
  change (if p 160 then d56 (change p 10000 none) else d7 (change p 10000 none)) = d57 p
  rw [sub7, sub3]
  rfl
theorem sub9 (p : Pattern) : d1 (change p 10000 none) = d1 p := by
  rfl
theorem sub10 (p : Pattern) : d8 (change p 10000 none) = d8 p := by
  change (if p 271 then d1 (change p 10000 none) else d0 (change p 10000 none)) = d8 p
  rw [sub9, sub0]
  rfl
theorem sub11 (p : Pattern) : d3 (change p 10000 none) = d3 p := by
  rfl
theorem sub12 (p : Pattern) : d9 (change p 10000 none) = d9 p := by
  change (if p 271 then d3 (change p 10000 none) else d2 (change p 10000 none)) = d9 p
  rw [sub11, sub1]
  rfl
theorem sub13 (p : Pattern) : d10 (change p 10000 none) = d10 p := by
  change (if p 193 then d9 (change p 10000 none) else d8 (change p 10000 none)) = d10 p
  rw [sub12, sub10]
  rfl
theorem sub14 (p : Pattern) : d11 (change p 10000 none) = d11 p := by
  change (if p 192 then d10 (change p 10000 none) else d8 (change p 10000 none)) = d11 p
  rw [sub13, sub10]
  rfl
theorem sub15 (p : Pattern) : d12 (change p 10000 none) = d12 p := by
  change (if p 168 then d11 (change p 10000 none) else d7 (change p 10000 none)) = d12 p
  rw [sub14, sub3]
  rfl
theorem sub16 (p : Pattern) : d5 (change p 10000 none) = d5 p := by
  rfl
theorem sub17 (p : Pattern) : d58 (change p 10000 none) = d58 p := by
  change (if p 271 then d5 (change p 10000 none) else d4 (change p 10000 none)) = d58 p
  rw [sub16, sub4]
  rfl
theorem sub18 (p : Pattern) : d59 (change p 10000 none) = d59 p := by
  change (if p 193 then d58 (change p 10000 none) else d9 (change p 10000 none)) = d59 p
  rw [sub17, sub12]
  rfl
theorem sub19 (p : Pattern) : d60 (change p 10000 none) = d60 p := by
  change (if p 192 then d59 (change p 10000 none) else d9 (change p 10000 none)) = d60 p
  rw [sub18, sub12]
  rfl
theorem sub20 (p : Pattern) : d61 (change p 10000 none) = d61 p := by
  change (if p 186 then d60 (change p 10000 none) else d11 (change p 10000 none)) = d61 p
  rw [sub19, sub14]
  rfl
theorem sub21 (p : Pattern) : d62 (change p 10000 none) = d62 p := by
  change (if p 168 then d61 (change p 10000 none) else d56 (change p 10000 none)) = d62 p
  rw [sub20, sub7]
  rfl
theorem sub22 (p : Pattern) : d63 (change p 10000 none) = d63 p := by
  change (if p 160 then d62 (change p 10000 none) else d12 (change p 10000 none)) = d63 p
  rw [sub21, sub15]
  rfl
theorem sub23 (p : Pattern) : d64 (change p 10000 none) = d64 p := by
  change (if p 141 then d63 (change p 10000 none) else d57 (change p 10000 none)) = d64 p
  rw [sub22, sub8]
  rfl
theorem sub24 (p : Pattern) : d65 (change p 10000 none) = d65 p := by
  change (if p 168 then d60 (change p 10000 none) else d55 (change p 10000 none)) = d65 p
  rw [sub19, sub6]
  rfl
theorem sub25 (p : Pattern) : d66 (change p 10000 none) = d66 p := by
  change (if p 141 then d65 (change p 10000 none) else d55 (change p 10000 none)) = d66 p
  rw [sub24, sub6]
  rfl
theorem sub26 (p : Pattern) : d67 (change p 10000 none) = d67 p := by
  change (if p 134 then d66 (change p 10000 none) else d64 (change p 10000 none)) = d67 p
  rw [sub25, sub23]
  rfl
theorem sub27 (p : Pattern) : d68 (change p 10000 none) = d68 p := by
  change (if p 158 then d55 (change p 10000 none) else d57 (change p 10000 none)) = d68 p
  rw [sub6, sub8]
  rfl
theorem sub28 (p : Pattern) : d69 (change p 10000 none) = d69 p := by
  change (if p 158 then d65 (change p 10000 none) else d63 (change p 10000 none)) = d69 p
  rw [sub24, sub22]
  rfl
theorem sub29 (p : Pattern) : d70 (change p 10000 none) = d70 p := by
  change (if p 141 then d69 (change p 10000 none) else d68 (change p 10000 none)) = d70 p
  rw [sub28, sub27]
  rfl
theorem sub30 (p : Pattern) : d71 (change p 10000 none) = d71 p := by
  change (if p 134 then d66 (change p 10000 none) else d70 (change p 10000 none)) = d71 p
  rw [sub25, sub29]
  rfl
theorem sub31 (p : Pattern) : d72 (change p 10000 none) = d72 p := by
  change (if p 133 then d71 (change p 10000 none) else d67 (change p 10000 none)) = d72 p
  rw [sub30, sub26]
  rfl
theorem sub32 (p : Pattern) : d73 (change p 10000 none) = d73 p := by
  change (if p 133 then d66 (change p 10000 none) else d71 (change p 10000 none)) = d73 p
  rw [sub25, sub30]
  rfl
theorem sub33 (p : Pattern) : d74 (change p 10000 none) = d74 p := by
  change (if p 132 then d73 (change p 10000 none) else d72 (change p 10000 none)) = d74 p
  rw [sub32, sub31]
  rfl
theorem sub34 (p : Pattern) : d75 (change p 10000 none) = d75 p := by
  change (if p 108 then d66 (change p 10000 none) else d74 (change p 10000 none)) = d75 p
  rw [sub25, sub33]
  rfl
theorem sub35 (p : Pattern) : d2 (change p 10000 (some 108)) = d2 p := by
  rfl
theorem sub36 (p : Pattern) : d4 (change p 10000 (some 108)) = d4 p := by
  rfl
theorem sub37 (p : Pattern) : d54 (change p 10000 (some 108)) = d54 p := by
  change (if p 193 then d4 (change p 10000 (some 108)) else d2 (change p 10000 (some 108))) = d54 p
  rw [sub36, sub35]
  rfl
theorem sub38 (p : Pattern) : d55 (change p 10000 (some 108)) = d55 p := by
  change (if p 192 then d54 (change p 10000 (some 108)) else d2 (change p 10000 (some 108))) = d55 p
  rw [sub37, sub35]
  rfl
theorem sub39 (p : Pattern) : d3 (change p 10000 (some 108)) = d3 p := by
  rfl
theorem sub40 (p : Pattern) : d9 (change p 10000 (some 108)) = d9 p := by
  change (if p 271 then d3 (change p 10000 (some 108)) else d2 (change p 10000 (some 108))) = d9 p
  rw [sub39, sub35]
  rfl
theorem sub41 (p : Pattern) : d5 (change p 10000 (some 108)) = d5 p := by
  rfl
theorem sub42 (p : Pattern) : d58 (change p 10000 (some 108)) = d58 p := by
  change (if p 271 then d5 (change p 10000 (some 108)) else d4 (change p 10000 (some 108))) = d58 p
  rw [sub41, sub36]
  rfl
theorem sub43 (p : Pattern) : d59 (change p 10000 (some 108)) = d59 p := by
  change (if p 193 then d58 (change p 10000 (some 108)) else d9 (change p 10000 (some 108))) = d59 p
  rw [sub42, sub40]
  rfl
theorem sub44 (p : Pattern) : d60 (change p 10000 (some 108)) = d60 p := by
  change (if p 192 then d59 (change p 10000 (some 108)) else d9 (change p 10000 (some 108))) = d60 p
  rw [sub43, sub40]
  rfl
theorem sub45 (p : Pattern) : d65 (change p 10000 (some 108)) = d65 p := by
  change (if p 168 then d60 (change p 10000 (some 108)) else d55 (change p 10000 (some 108))) = d65 p
  rw [sub44, sub38]
  rfl
theorem sub46 (p : Pattern) : d66 (change p 10000 (some 108)) = d66 p := by
  change (if p 141 then d65 (change p 10000 (some 108)) else d55 (change p 10000 (some 108))) = d66 p
  rw [sub45, sub38]
  rfl
theorem sub47 (p : Pattern) : d75 (change p 10000 (some 108)) = d66 p := by
  change d66 (change p 10000 (some 108)) = d66 p
  exact sub46 p
theorem sub48 (p : Pattern) : d2 (change p 108 (some 134)) = d2 p := by
  rfl
theorem sub49 (p : Pattern) : d4 (change p 108 (some 134)) = d4 p := by
  rfl
theorem sub50 (p : Pattern) : d54 (change p 108 (some 134)) = d54 p := by
  change (if p 193 then d4 (change p 108 (some 134)) else d2 (change p 108 (some 134))) = d54 p
  rw [sub49, sub48]
  rfl
theorem sub51 (p : Pattern) : d55 (change p 108 (some 134)) = d55 p := by
  change (if p 192 then d54 (change p 108 (some 134)) else d2 (change p 108 (some 134))) = d55 p
  rw [sub50, sub48]
  rfl
theorem sub52 (p : Pattern) : d3 (change p 108 (some 134)) = d3 p := by
  rfl
theorem sub53 (p : Pattern) : d9 (change p 108 (some 134)) = d9 p := by
  change (if p 271 then d3 (change p 108 (some 134)) else d2 (change p 108 (some 134))) = d9 p
  rw [sub52, sub48]
  rfl
theorem sub54 (p : Pattern) : d5 (change p 108 (some 134)) = d5 p := by
  rfl
theorem sub55 (p : Pattern) : d58 (change p 108 (some 134)) = d58 p := by
  change (if p 271 then d5 (change p 108 (some 134)) else d4 (change p 108 (some 134))) = d58 p
  rw [sub54, sub49]
  rfl
theorem sub56 (p : Pattern) : d59 (change p 108 (some 134)) = d59 p := by
  change (if p 193 then d58 (change p 108 (some 134)) else d9 (change p 108 (some 134))) = d59 p
  rw [sub55, sub53]
  rfl
theorem sub57 (p : Pattern) : d60 (change p 108 (some 134)) = d60 p := by
  change (if p 192 then d59 (change p 108 (some 134)) else d9 (change p 108 (some 134))) = d60 p
  rw [sub56, sub53]
  rfl
theorem sub58 (p : Pattern) : d65 (change p 108 (some 134)) = d65 p := by
  change (if p 168 then d60 (change p 108 (some 134)) else d55 (change p 108 (some 134))) = d65 p
  rw [sub57, sub51]
  rfl
theorem sub59 (p : Pattern) : d66 (change p 108 (some 134)) = d66 p := by
  change (if p 141 then d65 (change p 108 (some 134)) else d55 (change p 108 (some 134))) = d66 p
  rw [sub58, sub51]
  rfl
theorem sub60 (p : Pattern) : d67 (change p 108 (some 134)) = d66 p := by
  change d66 (change p 108 (some 134)) = d66 p
  exact sub59 p
theorem sub61 (p : Pattern) : d71 (change p 108 (some 134)) = d66 p := by
  change d66 (change p 108 (some 134)) = d66 p
  exact sub59 p
theorem sub62 (p : Pattern) : d72 (change p 108 (some 134)) = d66 p := by
  change (if p 133 then d71 (change p 108 (some 134)) else d67 (change p 108 (some 134))) = d66 p
  rw [sub61, sub60]
  simp only [ite_self]
theorem sub63 (p : Pattern) : d73 (change p 108 (some 134)) = d66 p := by
  change (if p 133 then d66 (change p 108 (some 134)) else d71 (change p 108 (some 134))) = d66 p
  rw [sub59, sub61]
  simp only [ite_self]
theorem sub64 (p : Pattern) : d74 (change p 108 (some 134)) = d66 p := by
  change (if p 132 then d73 (change p 108 (some 134)) else d72 (change p 108 (some 134))) = d66 p
  rw [sub63, sub62]
  simp only [ite_self]
theorem sub65 (p : Pattern) : d75 (change p 108 (some 134)) = d66 p := by
  change d74 (change p 108 (some 134)) = d66 p
  exact sub64 p
theorem sub66 (p : Pattern) : d106 (change p 10000 none) = d106 p := by
  change (if p 160 then d55 (change p 10000 none) else d7 (change p 10000 none)) = d106 p
  rw [sub6, sub3]
  rfl
theorem sub67 (p : Pattern) : d107 (change p 10000 none) = d107 p := by
  change (if p 159 then d55 (change p 10000 none) else d106 (change p 10000 none)) = d107 p
  rw [sub6, sub66]
  rfl
theorem sub68 (p : Pattern) : d108 (change p 10000 none) = d108 p := by
  change (if p 158 then d107 (change p 10000 none) else d106 (change p 10000 none)) = d108 p
  rw [sub67, sub66]
  rfl
theorem sub69 (p : Pattern) : d109 (change p 10000 none) = d109 p := by
  change (if p 160 then d65 (change p 10000 none) else d12 (change p 10000 none)) = d109 p
  rw [sub24, sub15]
  rfl
theorem sub70 (p : Pattern) : d110 (change p 10000 none) = d110 p := by
  change (if p 159 then d65 (change p 10000 none) else d109 (change p 10000 none)) = d110 p
  rw [sub24, sub69]
  rfl
theorem sub71 (p : Pattern) : d111 (change p 10000 none) = d111 p := by
  change (if p 158 then d110 (change p 10000 none) else d109 (change p 10000 none)) = d111 p
  rw [sub70, sub69]
  rfl
theorem sub72 (p : Pattern) : d112 (change p 10000 none) = d112 p := by
  change (if p 141 then d111 (change p 10000 none) else d108 (change p 10000 none)) = d112 p
  rw [sub71, sub68]
  rfl
theorem sub73 (p : Pattern) : d113 (change p 10000 none) = d113 p := by
  change (if p 134 then d112 (change p 10000 none) else d64 (change p 10000 none)) = d113 p
  rw [sub72, sub23]
  rfl
theorem sub74 (p : Pattern) : d114 (change p 10000 none) = d114 p := by
  change (if p 159 then d55 (change p 10000 none) else d57 (change p 10000 none)) = d114 p
  rw [sub6, sub8]
  rfl
theorem sub75 (p : Pattern) : d115 (change p 10000 none) = d115 p := by
  change (if p 158 then d114 (change p 10000 none) else d57 (change p 10000 none)) = d115 p
  rw [sub74, sub8]
  rfl
theorem sub76 (p : Pattern) : d116 (change p 10000 none) = d116 p := by
  change (if p 159 then d65 (change p 10000 none) else d63 (change p 10000 none)) = d116 p
  rw [sub24, sub22]
  rfl
theorem sub77 (p : Pattern) : d117 (change p 10000 none) = d117 p := by
  change (if p 158 then d116 (change p 10000 none) else d63 (change p 10000 none)) = d117 p
  rw [sub76, sub22]
  rfl
theorem sub78 (p : Pattern) : d118 (change p 10000 none) = d118 p := by
  change (if p 141 then d117 (change p 10000 none) else d115 (change p 10000 none)) = d118 p
  rw [sub77, sub75]
  rfl
theorem sub79 (p : Pattern) : d119 (change p 10000 none) = d119 p := by
  change (if p 187 then d55 (change p 10000 none) else d7 (change p 10000 none)) = d119 p
  rw [sub6, sub3]
  rfl
theorem sub80 (p : Pattern) : d120 (change p 10000 none) = d120 p := by
  change (if p 186 then d119 (change p 10000 none) else d7 (change p 10000 none)) = d120 p
  rw [sub79, sub3]
  rfl
theorem sub81 (p : Pattern) : d121 (change p 10000 none) = d121 p := by
  change (if p 160 then d55 (change p 10000 none) else d120 (change p 10000 none)) = d121 p
  rw [sub6, sub80]
  rfl
theorem sub82 (p : Pattern) : d122 (change p 10000 none) = d122 p := by
  change (if p 159 then d121 (change p 10000 none) else d106 (change p 10000 none)) = d122 p
  rw [sub81, sub66]
  rfl
theorem sub83 (p : Pattern) : d123 (change p 10000 none) = d123 p := by
  change (if p 159 then d55 (change p 10000 none) else d121 (change p 10000 none)) = d123 p
  rw [sub6, sub81]
  rfl
theorem sub84 (p : Pattern) : d124 (change p 10000 none) = d124 p := by
  change (if p 158 then d123 (change p 10000 none) else d122 (change p 10000 none)) = d124 p
  rw [sub83, sub82]
  rfl
theorem sub85 (p : Pattern) : d125 (change p 10000 none) = d125 p := by
  change (if p 187 then d60 (change p 10000 none) else d11 (change p 10000 none)) = d125 p
  rw [sub19, sub14]
  rfl
theorem sub86 (p : Pattern) : d126 (change p 10000 none) = d126 p := by
  change (if p 186 then d125 (change p 10000 none) else d11 (change p 10000 none)) = d126 p
  rw [sub85, sub14]
  rfl
theorem sub87 (p : Pattern) : d127 (change p 10000 none) = d127 p := by
  change (if p 168 then d126 (change p 10000 none) else d120 (change p 10000 none)) = d127 p
  rw [sub86, sub80]
  rfl
theorem sub88 (p : Pattern) : d128 (change p 10000 none) = d128 p := by
  change (if p 160 then d65 (change p 10000 none) else d127 (change p 10000 none)) = d128 p
  rw [sub24, sub87]
  rfl
theorem sub89 (p : Pattern) : d129 (change p 10000 none) = d129 p := by
  change (if p 159 then d128 (change p 10000 none) else d109 (change p 10000 none)) = d129 p
  rw [sub88, sub69]
  rfl
theorem sub90 (p : Pattern) : d130 (change p 10000 none) = d130 p := by
  change (if p 159 then d65 (change p 10000 none) else d128 (change p 10000 none)) = d130 p
  rw [sub24, sub88]
  rfl
theorem sub91 (p : Pattern) : d131 (change p 10000 none) = d131 p := by
  change (if p 158 then d130 (change p 10000 none) else d129 (change p 10000 none)) = d131 p
  rw [sub90, sub89]
  rfl
theorem sub92 (p : Pattern) : d132 (change p 10000 none) = d132 p := by
  change (if p 141 then d131 (change p 10000 none) else d124 (change p 10000 none)) = d132 p
  rw [sub91, sub84]
  rfl
theorem sub93 (p : Pattern) : d133 (change p 10000 none) = d133 p := by
  change (if p 134 then d132 (change p 10000 none) else d118 (change p 10000 none)) = d133 p
  rw [sub92, sub78]
  rfl
theorem sub94 (p : Pattern) : d134 (change p 10000 none) = d134 p := by
  change (if p 133 then d133 (change p 10000 none) else d113 (change p 10000 none)) = d134 p
  rw [sub93, sub73]
  rfl
theorem sub95 (p : Pattern) : d135 (change p 10000 none) = d135 p := by
  change (if p 133 then d66 (change p 10000 none) else d133 (change p 10000 none)) = d135 p
  rw [sub25, sub93]
  rfl
theorem sub96 (p : Pattern) : d136 (change p 10000 none) = d136 p := by
  change (if p 132 then d135 (change p 10000 none) else d134 (change p 10000 none)) = d136 p
  rw [sub95, sub94]
  rfl
theorem sub97 (p : Pattern) : d137 (change p 10000 none) = d137 p := by
  change (if p 186 then d55 (change p 10000 none) else d119 (change p 10000 none)) = d137 p
  rw [sub6, sub79]
  rfl
theorem sub98 (p : Pattern) : d138 (change p 10000 none) = d138 p := by
  change (if p 160 then d137 (change p 10000 none) else d7 (change p 10000 none)) = d138 p
  rw [sub97, sub3]
  rfl
theorem sub99 (p : Pattern) : d139 (change p 10000 none) = d139 p := by
  change (if p 160 then d137 (change p 10000 none) else d120 (change p 10000 none)) = d139 p
  rw [sub97, sub80]
  rfl
theorem sub100 (p : Pattern) : d140 (change p 10000 none) = d140 p := by
  change (if p 159 then d139 (change p 10000 none) else d138 (change p 10000 none)) = d140 p
  rw [sub99, sub98]
  rfl
theorem sub101 (p : Pattern) : d141 (change p 10000 none) = d141 p := by
  change (if p 159 then d55 (change p 10000 none) else d139 (change p 10000 none)) = d141 p
  rw [sub6, sub99]
  rfl
theorem sub102 (p : Pattern) : d142 (change p 10000 none) = d142 p := by
  change (if p 158 then d141 (change p 10000 none) else d140 (change p 10000 none)) = d142 p
  rw [sub101, sub100]
  rfl
theorem sub103 (p : Pattern) : d143 (change p 10000 none) = d143 p := by
  change (if p 186 then d60 (change p 10000 none) else d125 (change p 10000 none)) = d143 p
  rw [sub19, sub85]
  rfl
theorem sub104 (p : Pattern) : d144 (change p 10000 none) = d144 p := by
  change (if p 168 then d143 (change p 10000 none) else d137 (change p 10000 none)) = d144 p
  rw [sub103, sub97]
  rfl
theorem sub105 (p : Pattern) : d145 (change p 10000 none) = d145 p := by
  change (if p 160 then d144 (change p 10000 none) else d12 (change p 10000 none)) = d145 p
  rw [sub104, sub15]
  rfl
theorem sub106 (p : Pattern) : d146 (change p 10000 none) = d146 p := by
  change (if p 160 then d144 (change p 10000 none) else d127 (change p 10000 none)) = d146 p
  rw [sub104, sub87]
  rfl
theorem sub107 (p : Pattern) : d147 (change p 10000 none) = d147 p := by
  change (if p 159 then d146 (change p 10000 none) else d145 (change p 10000 none)) = d147 p
  rw [sub106, sub105]
  rfl
theorem sub108 (p : Pattern) : d148 (change p 10000 none) = d148 p := by
  change (if p 159 then d65 (change p 10000 none) else d146 (change p 10000 none)) = d148 p
  rw [sub24, sub106]
  rfl
theorem sub109 (p : Pattern) : d149 (change p 10000 none) = d149 p := by
  change (if p 158 then d148 (change p 10000 none) else d147 (change p 10000 none)) = d149 p
  rw [sub108, sub107]
  rfl
theorem sub110 (p : Pattern) : d150 (change p 10000 none) = d150 p := by
  change (if p 141 then d149 (change p 10000 none) else d142 (change p 10000 none)) = d150 p
  rw [sub109, sub102]
  rfl
theorem sub111 (p : Pattern) : d151 (change p 10000 none) = d151 p := by
  change (if p 134 then d66 (change p 10000 none) else d150 (change p 10000 none)) = d151 p
  rw [sub25, sub110]
  rfl
theorem sub112 (p : Pattern) : d152 (change p 10000 none) = d152 p := by
  change (if p 133 then d151 (change p 10000 none) else d67 (change p 10000 none)) = d152 p
  rw [sub111, sub26]
  rfl
theorem sub113 (p : Pattern) : d153 (change p 10000 none) = d153 p := by
  change (if p 159 then d139 (change p 10000 none) else d57 (change p 10000 none)) = d153 p
  rw [sub99, sub8]
  rfl
theorem sub114 (p : Pattern) : d154 (change p 10000 none) = d154 p := by
  change (if p 158 then d141 (change p 10000 none) else d153 (change p 10000 none)) = d154 p
  rw [sub101, sub113]
  rfl
theorem sub115 (p : Pattern) : d155 (change p 10000 none) = d155 p := by
  change (if p 159 then d146 (change p 10000 none) else d63 (change p 10000 none)) = d155 p
  rw [sub106, sub22]
  rfl
theorem sub116 (p : Pattern) : d156 (change p 10000 none) = d156 p := by
  change (if p 158 then d148 (change p 10000 none) else d155 (change p 10000 none)) = d156 p
  rw [sub108, sub115]
  rfl
theorem sub117 (p : Pattern) : d157 (change p 10000 none) = d157 p := by
  change (if p 141 then d156 (change p 10000 none) else d154 (change p 10000 none)) = d157 p
  rw [sub116, sub114]
  rfl
theorem sub118 (p : Pattern) : d158 (change p 10000 none) = d158 p := by
  change (if p 134 then d66 (change p 10000 none) else d157 (change p 10000 none)) = d158 p
  rw [sub25, sub117]
  rfl
theorem sub119 (p : Pattern) : d159 (change p 10000 none) = d159 p := by
  change (if p 133 then d66 (change p 10000 none) else d158 (change p 10000 none)) = d159 p
  rw [sub25, sub118]
  rfl
end NetHack.Sokoban12CostPartition
