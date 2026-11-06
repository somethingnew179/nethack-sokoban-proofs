/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Roots
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub0 (p : Pattern) : d0 (change p 10000 none) = d0 p := by
  rfl
theorem sub1 (p : Pattern) : d12 (change p 10000 none) = d12 p := by
  rfl
theorem sub2 (p : Pattern) : d13 (change p 10000 none) = d13 p := by
  change (if p 247 then d12 (change p 10000 none) else d0 (change p 10000 none)) = d13 p
  rw [sub1, sub0]
  rfl
theorem sub3 (p : Pattern) : d14 (change p 10000 none) = d14 p := by
  change (if p 246 then d13 (change p 10000 none) else d0 (change p 10000 none)) = d14 p
  rw [sub2, sub0]
  rfl
theorem sub4 (p : Pattern) : d15 (change p 10000 none) = d15 p := by
  change (if p 204 then d12 (change p 10000 none) else d14 (change p 10000 none)) = d15 p
  rw [sub1, sub3]
  rfl
theorem sub5 (p : Pattern) : d16 (change p 10000 none) = d16 p := by
  change (if p 182 then d15 (change p 10000 none) else d14 (change p 10000 none)) = d16 p
  rw [sub4, sub3]
  rfl
theorem sub6 (p : Pattern) : d4 (change p 10000 none) = d4 p := by
  rfl
theorem sub7 (p : Pattern) : d17 (change p 10000 none) = d17 p := by
  change (if p 247 then d12 (change p 10000 none) else d4 (change p 10000 none)) = d17 p
  rw [sub1, sub6]
  rfl
theorem sub8 (p : Pattern) : d18 (change p 10000 none) = d18 p := by
  change (if p 246 then d17 (change p 10000 none) else d4 (change p 10000 none)) = d18 p
  rw [sub7, sub6]
  rfl
theorem sub9 (p : Pattern) : d19 (change p 10000 none) = d19 p := by
  change (if p 204 then d12 (change p 10000 none) else d18 (change p 10000 none)) = d19 p
  rw [sub1, sub8]
  rfl
theorem sub10 (p : Pattern) : d20 (change p 10000 none) = d20 p := by
  change (if p 182 then d19 (change p 10000 none) else d18 (change p 10000 none)) = d20 p
  rw [sub9, sub8]
  rfl
theorem sub11 (p : Pattern) : d21 (change p 10000 none) = d21 p := by
  change (if p 163 then d20 (change p 10000 none) else d16 (change p 10000 none)) = d21 p
  rw [sub10, sub5]
  rfl
theorem sub12 (p : Pattern) : d22 (change p 10000 none) = d22 p := by
  change (if p 162 then d21 (change p 10000 none) else d16 (change p 10000 none)) = d22 p
  rw [sub11, sub5]
  rfl
theorem sub13 (p : Pattern) : d9 (change p 10000 none) = d9 p := by
  rfl
theorem sub14 (p : Pattern) : d23 (change p 10000 none) = d23 p := by
  change (if p 247 then d12 (change p 10000 none) else d9 (change p 10000 none)) = d23 p
  rw [sub1, sub13]
  rfl
theorem sub15 (p : Pattern) : d24 (change p 10000 none) = d24 p := by
  change (if p 246 then d23 (change p 10000 none) else d9 (change p 10000 none)) = d24 p
  rw [sub14, sub13]
  rfl
theorem sub16 (p : Pattern) : d25 (change p 10000 none) = d25 p := by
  change (if p 204 then d12 (change p 10000 none) else d24 (change p 10000 none)) = d25 p
  rw [sub1, sub15]
  rfl
theorem sub17 (p : Pattern) : d26 (change p 10000 none) = d26 p := by
  change (if p 182 then d25 (change p 10000 none) else d24 (change p 10000 none)) = d26 p
  rw [sub16, sub15]
  rfl
theorem sub18 (p : Pattern) : d27 (change p 10000 none) = d27 p := by
  change (if p 163 then d12 (change p 10000 none) else d26 (change p 10000 none)) = d27 p
  rw [sub1, sub17]
  rfl
theorem sub19 (p : Pattern) : d28 (change p 10000 none) = d28 p := by
  change (if p 162 then d27 (change p 10000 none) else d21 (change p 10000 none)) = d28 p
  rw [sub18, sub11]
  rfl
theorem sub20 (p : Pattern) : d29 (change p 10000 none) = d29 p := by
  change (if p 161 then d28 (change p 10000 none) else d22 (change p 10000 none)) = d29 p
  rw [sub19, sub12]
  rfl
theorem sub21 (p : Pattern) : d2 (change p 10000 none) = d2 p := by
  rfl
theorem sub22 (p : Pattern) : d30 (change p 10000 none) = d30 p := by
  change (if p 247 then d12 (change p 10000 none) else d2 (change p 10000 none)) = d30 p
  rw [sub1, sub21]
  rfl
theorem sub23 (p : Pattern) : d31 (change p 10000 none) = d31 p := by
  change (if p 246 then d30 (change p 10000 none) else d2 (change p 10000 none)) = d31 p
  rw [sub22, sub21]
  rfl
theorem sub24 (p : Pattern) : d32 (change p 10000 none) = d32 p := by
  change (if p 204 then d12 (change p 10000 none) else d31 (change p 10000 none)) = d32 p
  rw [sub1, sub23]
  rfl
theorem sub25 (p : Pattern) : d33 (change p 10000 none) = d33 p := by
  change (if p 182 then d32 (change p 10000 none) else d14 (change p 10000 none)) = d33 p
  rw [sub24, sub3]
  rfl
theorem sub26 (p : Pattern) : d6 (change p 10000 none) = d6 p := by
  rfl
theorem sub27 (p : Pattern) : d34 (change p 10000 none) = d34 p := by
  change (if p 247 then d12 (change p 10000 none) else d6 (change p 10000 none)) = d34 p
  rw [sub1, sub26]
  rfl
theorem sub28 (p : Pattern) : d35 (change p 10000 none) = d35 p := by
  change (if p 246 then d34 (change p 10000 none) else d6 (change p 10000 none)) = d35 p
  rw [sub27, sub26]
  rfl
theorem sub29 (p : Pattern) : d36 (change p 10000 none) = d36 p := by
  change (if p 204 then d12 (change p 10000 none) else d35 (change p 10000 none)) = d36 p
  rw [sub1, sub28]
  rfl
theorem sub30 (p : Pattern) : d37 (change p 10000 none) = d37 p := by
  change (if p 182 then d36 (change p 10000 none) else d14 (change p 10000 none)) = d37 p
  rw [sub29, sub3]
  rfl
theorem sub31 (p : Pattern) : d38 (change p 10000 none) = d38 p := by
  change (if p 163 then d37 (change p 10000 none) else d33 (change p 10000 none)) = d38 p
  rw [sub30, sub25]
  rfl
theorem sub32 (p : Pattern) : d11 (change p 10000 none) = d11 p := by
  rfl
theorem sub33 (p : Pattern) : d39 (change p 10000 none) = d39 p := by
  change (if p 247 then d12 (change p 10000 none) else d11 (change p 10000 none)) = d39 p
  rw [sub1, sub32]
  rfl
theorem sub34 (p : Pattern) : d40 (change p 10000 none) = d40 p := by
  change (if p 246 then d39 (change p 10000 none) else d11 (change p 10000 none)) = d40 p
  rw [sub33, sub32]
  rfl
theorem sub35 (p : Pattern) : d41 (change p 10000 none) = d41 p := by
  change (if p 204 then d12 (change p 10000 none) else d40 (change p 10000 none)) = d41 p
  rw [sub1, sub34]
  rfl
theorem sub36 (p : Pattern) : d42 (change p 10000 none) = d42 p := by
  change (if p 182 then d41 (change p 10000 none) else d14 (change p 10000 none)) = d42 p
  rw [sub35, sub3]
  rfl
theorem sub37 (p : Pattern) : d43 (change p 10000 none) = d43 p := by
  change (if p 182 then d12 (change p 10000 none) else d18 (change p 10000 none)) = d43 p
  rw [sub1, sub8]
  rfl
theorem sub38 (p : Pattern) : d44 (change p 10000 none) = d44 p := by
  change (if p 163 then d43 (change p 10000 none) else d42 (change p 10000 none)) = d44 p
  rw [sub37, sub36]
  rfl
theorem sub39 (p : Pattern) : d45 (change p 10000 none) = d45 p := by
  change (if p 162 then d44 (change p 10000 none) else d38 (change p 10000 none)) = d45 p
  rw [sub38, sub31]
  rfl
theorem sub40 (p : Pattern) : d46 (change p 10000 none) = d46 p := by
  change (if p 182 then d12 (change p 10000 none) else d14 (change p 10000 none)) = d46 p
  rw [sub1, sub3]
  rfl
theorem sub41 (p : Pattern) : d47 (change p 10000 none) = d47 p := by
  change (if p 163 then d43 (change p 10000 none) else d46 (change p 10000 none)) = d47 p
  rw [sub37, sub40]
  rfl
theorem sub42 (p : Pattern) : d48 (change p 10000 none) = d48 p := by
  change (if p 182 then d12 (change p 10000 none) else d24 (change p 10000 none)) = d48 p
  rw [sub1, sub15]
  rfl
theorem sub43 (p : Pattern) : d49 (change p 10000 none) = d49 p := by
  change (if p 163 then d12 (change p 10000 none) else d48 (change p 10000 none)) = d49 p
  rw [sub1, sub42]
  rfl
theorem sub44 (p : Pattern) : d50 (change p 10000 none) = d50 p := by
  change (if p 162 then d49 (change p 10000 none) else d47 (change p 10000 none)) = d50 p
  rw [sub43, sub41]
  rfl
theorem sub45 (p : Pattern) : d51 (change p 10000 none) = d51 p := by
  change (if p 161 then d50 (change p 10000 none) else d45 (change p 10000 none)) = d51 p
  rw [sub44, sub39]
  rfl
theorem sub46 (p : Pattern) : d52 (change p 10000 none) = d52 p := by
  change (if p 160 then d51 (change p 10000 none) else d29 (change p 10000 none)) = d52 p
  rw [sub45, sub20]
  rfl
theorem sub47 (p : Pattern) : d53 (change p 10000 none) = d53 p := by
  change (if p 182 then d32 (change p 10000 none) else d31 (change p 10000 none)) = d53 p
  rw [sub24, sub23]
  rfl
theorem sub48 (p : Pattern) : d54 (change p 10000 none) = d54 p := by
  change (if p 163 then d53 (change p 10000 none) else d16 (change p 10000 none)) = d54 p
  rw [sub47, sub5]
  rfl
theorem sub49 (p : Pattern) : d55 (change p 10000 none) = d55 p := by
  change (if p 163 then d26 (change p 10000 none) else d20 (change p 10000 none)) = d55 p
  rw [sub17, sub10]
  rfl
theorem sub50 (p : Pattern) : d56 (change p 10000 none) = d56 p := by
  change (if p 162 then d55 (change p 10000 none) else d54 (change p 10000 none)) = d56 p
  rw [sub49, sub48]
  rfl
theorem sub51 (p : Pattern) : d10 (change p 10000 none) = d10 p := by
  rfl
theorem sub52 (p : Pattern) : d57 (change p 10000 none) = d57 p := by
  change (if p 247 then d12 (change p 10000 none) else d10 (change p 10000 none)) = d57 p
  rw [sub1, sub51]
  rfl
theorem sub53 (p : Pattern) : d58 (change p 10000 none) = d58 p := by
  change (if p 246 then d57 (change p 10000 none) else d10 (change p 10000 none)) = d58 p
  rw [sub52, sub51]
  rfl
theorem sub54 (p : Pattern) : d59 (change p 10000 none) = d59 p := by
  change (if p 204 then d12 (change p 10000 none) else d58 (change p 10000 none)) = d59 p
  rw [sub1, sub53]
  rfl
theorem sub55 (p : Pattern) : d60 (change p 10000 none) = d60 p := by
  change (if p 182 then d59 (change p 10000 none) else d58 (change p 10000 none)) = d60 p
  rw [sub54, sub53]
  rfl
theorem sub56 (p : Pattern) : d61 (change p 10000 none) = d61 p := by
  change (if p 163 then d60 (change p 10000 none) else d20 (change p 10000 none)) = d61 p
  rw [sub55, sub10]
  rfl
theorem sub57 (p : Pattern) : d62 (change p 10000 none) = d62 p := by
  change (if p 182 then d41 (change p 10000 none) else d40 (change p 10000 none)) = d62 p
  rw [sub35, sub34]
  rfl
theorem sub58 (p : Pattern) : d63 (change p 10000 none) = d63 p := by
  change (if p 163 then d12 (change p 10000 none) else d62 (change p 10000 none)) = d63 p
  rw [sub1, sub57]
  rfl
theorem sub59 (p : Pattern) : d64 (change p 10000 none) = d64 p := by
  change (if p 162 then d63 (change p 10000 none) else d61 (change p 10000 none)) = d64 p
  rw [sub58, sub56]
  rfl
theorem sub60 (p : Pattern) : d65 (change p 10000 none) = d65 p := by
  change (if p 161 then d64 (change p 10000 none) else d56 (change p 10000 none)) = d65 p
  rw [sub59, sub50]
  rfl
theorem sub61 (p : Pattern) : d66 (change p 10000 none) = d66 p := by
  change (if p 182 then d12 (change p 10000 none) else d31 (change p 10000 none)) = d66 p
  rw [sub1, sub23]
  rfl
theorem sub62 (p : Pattern) : d67 (change p 10000 none) = d67 p := by
  change (if p 163 then d66 (change p 10000 none) else d37 (change p 10000 none)) = d67 p
  rw [sub61, sub30]
  rfl
theorem sub63 (p : Pattern) : d68 (change p 10000 none) = d68 p := by
  change (if p 163 then d48 (change p 10000 none) else d43 (change p 10000 none)) = d68 p
  rw [sub42, sub37]
  rfl
theorem sub64 (p : Pattern) : d69 (change p 10000 none) = d69 p := by
  change (if p 162 then d68 (change p 10000 none) else d67 (change p 10000 none)) = d69 p
  rw [sub63, sub62]
  rfl
theorem sub65 (p : Pattern) : d70 (change p 10000 none) = d70 p := by
  change (if p 182 then d12 (change p 10000 none) else d58 (change p 10000 none)) = d70 p
  rw [sub1, sub53]
  rfl
theorem sub66 (p : Pattern) : d71 (change p 10000 none) = d71 p := by
  change (if p 163 then d70 (change p 10000 none) else d43 (change p 10000 none)) = d71 p
  rw [sub65, sub37]
  rfl
theorem sub67 (p : Pattern) : d72 (change p 10000 none) = d72 p := by
  change (if p 182 then d12 (change p 10000 none) else d40 (change p 10000 none)) = d72 p
  rw [sub1, sub34]
  rfl
theorem sub68 (p : Pattern) : d73 (change p 10000 none) = d73 p := by
  change (if p 163 then d12 (change p 10000 none) else d72 (change p 10000 none)) = d73 p
  rw [sub1, sub67]
  rfl
theorem sub69 (p : Pattern) : d74 (change p 10000 none) = d74 p := by
  change (if p 162 then d73 (change p 10000 none) else d71 (change p 10000 none)) = d74 p
  rw [sub68, sub66]
  rfl
theorem sub70 (p : Pattern) : d75 (change p 10000 none) = d75 p := by
  change (if p 161 then d74 (change p 10000 none) else d69 (change p 10000 none)) = d75 p
  rw [sub69, sub64]
  rfl
theorem sub71 (p : Pattern) : d76 (change p 10000 none) = d76 p := by
  change (if p 160 then d75 (change p 10000 none) else d65 (change p 10000 none)) = d76 p
  rw [sub70, sub60]
  rfl
theorem sub72 (p : Pattern) : d77 (change p 10000 none) = d77 p := by
  change (if p 141 then d76 (change p 10000 none) else d52 (change p 10000 none)) = d77 p
  rw [sub71, sub46]
  rfl
theorem sub73 (p : Pattern) : d78 (change p 10000 none) = d78 p := by
  change (if p 182 then d36 (change p 10000 none) else d35 (change p 10000 none)) = d78 p
  rw [sub29, sub28]
  rfl
theorem sub74 (p : Pattern) : d79 (change p 10000 none) = d79 p := by
  change (if p 163 then d78 (change p 10000 none) else d53 (change p 10000 none)) = d79 p
  rw [sub73, sub47]
  rfl
theorem sub75 (p : Pattern) : d80 (change p 10000 none) = d80 p := by
  change (if p 162 then d63 (change p 10000 none) else d79 (change p 10000 none)) = d80 p
  rw [sub58, sub74]
  rfl
theorem sub76 (p : Pattern) : d81 (change p 10000 none) = d81 p := by
  change (if p 161 then d12 (change p 10000 none) else d80 (change p 10000 none)) = d81 p
  rw [sub1, sub75]
  rfl
theorem sub77 (p : Pattern) : d82 (change p 10000 none) = d82 p := by
  change (if p 160 then d81 (change p 10000 none) else d29 (change p 10000 none)) = d82 p
  rw [sub76, sub20]
  rfl
theorem sub78 (p : Pattern) : d83 (change p 10000 none) = d83 p := by
  change (if p 163 then d12 (change p 10000 none) else d78 (change p 10000 none)) = d83 p
  rw [sub1, sub73]
  rfl
theorem sub79 (p : Pattern) : d84 (change p 10000 none) = d84 p := by
  change (if p 162 then d12 (change p 10000 none) else d83 (change p 10000 none)) = d84 p
  rw [sub1, sub78]
  rfl
theorem sub80 (p : Pattern) : d85 (change p 10000 none) = d85 p := by
  change (if p 161 then d12 (change p 10000 none) else d84 (change p 10000 none)) = d85 p
  rw [sub1, sub79]
  rfl
theorem sub81 (p : Pattern) : d86 (change p 10000 none) = d86 p := by
  change (if p 160 then d85 (change p 10000 none) else d65 (change p 10000 none)) = d86 p
  rw [sub80, sub60]
  rfl
theorem sub82 (p : Pattern) : d87 (change p 10000 none) = d87 p := by
  change (if p 141 then d86 (change p 10000 none) else d82 (change p 10000 none)) = d87 p
  rw [sub81, sub77]
  rfl
theorem sub83 (p : Pattern) : d88 (change p 10000 none) = d88 p := by
  change (if p 138 then d87 (change p 10000 none) else d77 (change p 10000 none)) = d88 p
  rw [sub82, sub72]
  rfl
theorem sub84 (p : Pattern) : d89 (change p 10000 none) = d89 p := by
  change (if p 163 then d62 (change p 10000 none) else d26 (change p 10000 none)) = d89 p
  rw [sub57, sub17]
  rfl
theorem sub85 (p : Pattern) : d90 (change p 10000 none) = d90 p := by
  change (if p 162 then d63 (change p 10000 none) else d89 (change p 10000 none)) = d90 p
  rw [sub58, sub84]
  rfl
theorem sub86 (p : Pattern) : d91 (change p 10000 none) = d91 p := by
  change (if p 162 then d12 (change p 10000 none) else d63 (change p 10000 none)) = d91 p
  rw [sub1, sub58]
  rfl
theorem sub87 (p : Pattern) : d92 (change p 10000 none) = d92 p := by
  change (if p 161 then d91 (change p 10000 none) else d90 (change p 10000 none)) = d92 p
  rw [sub86, sub85]
  rfl
theorem sub88 (p : Pattern) : d93 (change p 10000 none) = d93 p := by
  change (if p 161 then d12 (change p 10000 none) else d91 (change p 10000 none)) = d93 p
  rw [sub1, sub86]
  rfl
theorem sub89 (p : Pattern) : d94 (change p 10000 none) = d94 p := by
  change (if p 160 then d93 (change p 10000 none) else d92 (change p 10000 none)) = d94 p
  rw [sub88, sub87]
  rfl
theorem sub90 (p : Pattern) : d95 (change p 10000 none) = d95 p := by
  change (if p 160 then d12 (change p 10000 none) else d93 (change p 10000 none)) = d95 p
  rw [sub1, sub88]
  rfl
theorem sub91 (p : Pattern) : d96 (change p 10000 none) = d96 p := by
  change (if p 141 then d95 (change p 10000 none) else d94 (change p 10000 none)) = d96 p
  rw [sub90, sub89]
  rfl
theorem sub92 (p : Pattern) : d97 (change p 10000 none) = d97 p := by
  change (if p 138 then d96 (change p 10000 none) else d87 (change p 10000 none)) = d97 p
  rw [sub91, sub82]
  rfl
theorem sub93 (p : Pattern) : d98 (change p 10000 none) = d98 p := by
  change (if p 116 then d97 (change p 10000 none) else d88 (change p 10000 none)) = d98 p
  rw [sub92, sub83]
  rfl
theorem sub94 (p : Pattern) : d99 (change p 10000 none) = d99 p := by
  change (if p 138 then d12 (change p 10000 none) else d87 (change p 10000 none)) = d99 p
  rw [sub1, sub82]
  rfl
theorem sub95 (p : Pattern) : d100 (change p 10000 none) = d100 p := by
  change (if p 116 then d99 (change p 10000 none) else d88 (change p 10000 none)) = d100 p
  rw [sub94, sub83]
  rfl
theorem sub96 (p : Pattern) : d101 (change p 10000 none) = d101 p := by
  change (if p 115 then d100 (change p 10000 none) else d98 (change p 10000 none)) = d101 p
  rw [sub95, sub93]
  rfl
theorem sub97 (p : Pattern) : d1 (change p 10000 none) = d1 p := by
  rfl
theorem sub98 (p : Pattern) : d102 (change p 10000 none) = d102 p := by
  change (if p 247 then d12 (change p 10000 none) else d1 (change p 10000 none)) = d102 p
  rw [sub1, sub97]
  rfl
theorem sub99 (p : Pattern) : d103 (change p 10000 none) = d103 p := by
  change (if p 246 then d102 (change p 10000 none) else d1 (change p 10000 none)) = d103 p
  rw [sub98, sub97]
  rfl
theorem sub100 (p : Pattern) : d104 (change p 10000 none) = d104 p := by
  change (if p 204 then d12 (change p 10000 none) else d103 (change p 10000 none)) = d104 p
  rw [sub1, sub99]
  rfl
theorem sub101 (p : Pattern) : d105 (change p 10000 none) = d105 p := by
  change (if p 182 then d104 (change p 10000 none) else d103 (change p 10000 none)) = d105 p
  rw [sub100, sub99]
  rfl
theorem sub102 (p : Pattern) : d5 (change p 10000 none) = d5 p := by
  rfl
theorem sub103 (p : Pattern) : d106 (change p 10000 none) = d106 p := by
  change (if p 247 then d12 (change p 10000 none) else d5 (change p 10000 none)) = d106 p
  rw [sub1, sub102]
  rfl
theorem sub104 (p : Pattern) : d107 (change p 10000 none) = d107 p := by
  change (if p 246 then d106 (change p 10000 none) else d5 (change p 10000 none)) = d107 p
  rw [sub103, sub102]
  rfl
theorem sub105 (p : Pattern) : d108 (change p 10000 none) = d108 p := by
  change (if p 204 then d12 (change p 10000 none) else d107 (change p 10000 none)) = d108 p
  rw [sub1, sub104]
  rfl
theorem sub106 (p : Pattern) : d109 (change p 10000 none) = d109 p := by
  change (if p 182 then d108 (change p 10000 none) else d107 (change p 10000 none)) = d109 p
  rw [sub105, sub104]
  rfl
theorem sub107 (p : Pattern) : d110 (change p 10000 none) = d110 p := by
  change (if p 163 then d109 (change p 10000 none) else d105 (change p 10000 none)) = d110 p
  rw [sub106, sub101]
  rfl
theorem sub108 (p : Pattern) : d111 (change p 10000 none) = d111 p := by
  change (if p 162 then d110 (change p 10000 none) else d105 (change p 10000 none)) = d111 p
  rw [sub107, sub101]
  rfl
theorem sub109 (p : Pattern) : d112 (change p 10000 none) = d112 p := by
  change (if p 163 then d12 (change p 10000 none) else d60 (change p 10000 none)) = d112 p
  rw [sub1, sub55]
  rfl
theorem sub110 (p : Pattern) : d113 (change p 10000 none) = d113 p := by
  change (if p 162 then d112 (change p 10000 none) else d110 (change p 10000 none)) = d113 p
  rw [sub109, sub107]
  rfl
theorem sub111 (p : Pattern) : d114 (change p 10000 none) = d114 p := by
  change (if p 161 then d113 (change p 10000 none) else d111 (change p 10000 none)) = d114 p
  rw [sub110, sub108]
  rfl
theorem sub112 (p : Pattern) : d3 (change p 10000 none) = d3 p := by
  rfl
theorem sub113 (p : Pattern) : d115 (change p 10000 none) = d115 p := by
  change (if p 247 then d12 (change p 10000 none) else d3 (change p 10000 none)) = d115 p
  rw [sub1, sub112]
  rfl
theorem sub114 (p : Pattern) : d116 (change p 10000 none) = d116 p := by
  change (if p 246 then d115 (change p 10000 none) else d3 (change p 10000 none)) = d116 p
  rw [sub113, sub112]
  rfl
theorem sub115 (p : Pattern) : d117 (change p 10000 none) = d117 p := by
  change (if p 204 then d12 (change p 10000 none) else d116 (change p 10000 none)) = d117 p
  rw [sub1, sub114]
  rfl
theorem sub116 (p : Pattern) : d118 (change p 10000 none) = d118 p := by
  change (if p 182 then d117 (change p 10000 none) else d103 (change p 10000 none)) = d118 p
  rw [sub115, sub99]
  rfl
theorem sub117 (p : Pattern) : d7 (change p 10000 none) = d7 p := by
  rfl
theorem sub118 (p : Pattern) : d119 (change p 10000 none) = d119 p := by
  change (if p 247 then d12 (change p 10000 none) else d7 (change p 10000 none)) = d119 p
  rw [sub1, sub117]
  rfl
theorem sub119 (p : Pattern) : d120 (change p 10000 none) = d120 p := by
  change (if p 246 then d119 (change p 10000 none) else d7 (change p 10000 none)) = d120 p
  rw [sub118, sub117]
  rfl
end NetHack.Sokoban22Refined85
