/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Roots
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub0 (p : Pattern) : d0 (change p 10000 (some 80)) = d0 p := by
  rfl
theorem sub1 (p : Pattern) : d2 (change p 10000 (some 80)) = d2 p := by
  rfl
theorem sub2 (p : Pattern) : d3 (change p 10000 (some 80)) = d3 p := by
  change (if p 161 then d2 (change p 10000 (some 80)) else d0 (change p 10000 (some 80))) = d3 p
  rw [sub1, sub0]
  rfl
theorem sub3 (p : Pattern) : d4 (change p 10000 (some 80)) = d4 p := by
  change (if p 160 then d3 (change p 10000 (some 80)) else d0 (change p 10000 (some 80))) = d4 p
  rw [sub2, sub0]
  rfl
theorem sub4 (p : Pattern) : d5 (change p 10000 (some 80)) = d5 p := by
  change (if p 160 then d2 (change p 10000 (some 80)) else d0 (change p 10000 (some 80))) = d5 p
  rw [sub1, sub0]
  rfl
theorem sub5 (p : Pattern) : d6 (change p 10000 (some 80)) = d6 p := by
  change (if p 159 then d5 (change p 10000 (some 80)) else d4 (change p 10000 (some 80))) = d6 p
  rw [sub4, sub3]
  rfl
theorem sub6 (p : Pattern) : d7 (change p 10000 (some 80)) = d7 p := by
  change (if p 159 then d2 (change p 10000 (some 80)) else d4 (change p 10000 (some 80))) = d7 p
  rw [sub1, sub3]
  rfl
theorem sub7 (p : Pattern) : d8 (change p 10000 (some 80)) = d8 p := by
  change (if p 158 then d7 (change p 10000 (some 80)) else d6 (change p 10000 (some 80))) = d8 p
  rw [sub6, sub5]
  rfl
theorem sub8 (p : Pattern) : d1 (change p 10000 (some 80)) = d1 p := by
  rfl
theorem sub9 (p : Pattern) : d9 (change p 10000 (some 80)) = d9 p := by
  change (if p 161 then d2 (change p 10000 (some 80)) else d1 (change p 10000 (some 80))) = d9 p
  rw [sub1, sub8]
  rfl
theorem sub10 (p : Pattern) : d10 (change p 10000 (some 80)) = d10 p := by
  change (if p 160 then d9 (change p 10000 (some 80)) else d1 (change p 10000 (some 80))) = d10 p
  rw [sub9, sub8]
  rfl
theorem sub11 (p : Pattern) : d11 (change p 10000 (some 80)) = d11 p := by
  change (if p 160 then d2 (change p 10000 (some 80)) else d1 (change p 10000 (some 80))) = d11 p
  rw [sub1, sub8]
  rfl
theorem sub12 (p : Pattern) : d12 (change p 10000 (some 80)) = d12 p := by
  change (if p 159 then d11 (change p 10000 (some 80)) else d10 (change p 10000 (some 80))) = d12 p
  rw [sub11, sub10]
  rfl
theorem sub13 (p : Pattern) : d13 (change p 10000 (some 80)) = d13 p := by
  change (if p 159 then d2 (change p 10000 (some 80)) else d10 (change p 10000 (some 80))) = d13 p
  rw [sub1, sub10]
  rfl
theorem sub14 (p : Pattern) : d14 (change p 10000 (some 80)) = d14 p := by
  change (if p 158 then d13 (change p 10000 (some 80)) else d12 (change p 10000 (some 80))) = d14 p
  rw [sub13, sub12]
  rfl
theorem sub15 (p : Pattern) : d15 (change p 10000 (some 80)) = d15 p := by
  change (if p 139 then d14 (change p 10000 (some 80)) else d8 (change p 10000 (some 80))) = d15 p
  rw [sub14, sub7]
  rfl
theorem sub16 (p : Pattern) : d16 (change p 10000 (some 80)) = d16 p := by
  change (if p 138 then d15 (change p 10000 (some 80)) else d8 (change p 10000 (some 80))) = d16 p
  rw [sub15, sub7]
  rfl
theorem sub17 (p : Pattern) : d17 (change p 10000 (some 80)) = d17 p := by
  change (if p 160 then d2 (change p 10000 (some 80)) else d3 (change p 10000 (some 80))) = d17 p
  rw [sub1, sub2]
  rfl
theorem sub18 (p : Pattern) : d18 (change p 10000 (some 80)) = d18 p := by
  change (if p 159 then d17 (change p 10000 (some 80)) else d4 (change p 10000 (some 80))) = d18 p
  rw [sub17, sub3]
  rfl
theorem sub19 (p : Pattern) : d19 (change p 10000 (some 80)) = d19 p := by
  change (if p 159 then d2 (change p 10000 (some 80)) else d17 (change p 10000 (some 80))) = d19 p
  rw [sub1, sub17]
  rfl
theorem sub20 (p : Pattern) : d20 (change p 10000 (some 80)) = d20 p := by
  change (if p 158 then d19 (change p 10000 (some 80)) else d18 (change p 10000 (some 80))) = d20 p
  rw [sub19, sub18]
  rfl
theorem sub21 (p : Pattern) : d21 (change p 10000 (some 80)) = d21 p := by
  change (if p 160 then d2 (change p 10000 (some 80)) else d9 (change p 10000 (some 80))) = d21 p
  rw [sub1, sub9]
  rfl
theorem sub22 (p : Pattern) : d22 (change p 10000 (some 80)) = d22 p := by
  change (if p 159 then d21 (change p 10000 (some 80)) else d10 (change p 10000 (some 80))) = d22 p
  rw [sub21, sub10]
  rfl
theorem sub23 (p : Pattern) : d23 (change p 10000 (some 80)) = d23 p := by
  change (if p 159 then d2 (change p 10000 (some 80)) else d21 (change p 10000 (some 80))) = d23 p
  rw [sub1, sub21]
  rfl
theorem sub24 (p : Pattern) : d24 (change p 10000 (some 80)) = d24 p := by
  change (if p 158 then d23 (change p 10000 (some 80)) else d22 (change p 10000 (some 80))) = d24 p
  rw [sub23, sub22]
  rfl
theorem sub25 (p : Pattern) : d25 (change p 10000 (some 80)) = d25 p := by
  change (if p 139 then d24 (change p 10000 (some 80)) else d20 (change p 10000 (some 80))) = d25 p
  rw [sub24, sub20]
  rfl
theorem sub26 (p : Pattern) : d26 (change p 10000 (some 80)) = d26 p := by
  change (if p 138 then d25 (change p 10000 (some 80)) else d20 (change p 10000 (some 80))) = d26 p
  rw [sub25, sub20]
  rfl
theorem sub27 (p : Pattern) : d27 (change p 10000 (some 80)) = d27 p := by
  change (if p 134 then d26 (change p 10000 (some 80)) else d16 (change p 10000 (some 80))) = d27 p
  rw [sub26, sub16]
  rfl
theorem sub28 (p : Pattern) : d28 (change p 10000 (some 80)) = d28 p := by
  change (if p 133 then d27 (change p 10000 (some 80)) else d16 (change p 10000 (some 80))) = d28 p
  rw [sub27, sub16]
  rfl
theorem sub29 (p : Pattern) : d29 (change p 10000 (some 80)) = d29 p := by
  change (if p 161 then d1 (change p 10000 (some 80)) else d0 (change p 10000 (some 80))) = d29 p
  rw [sub8, sub0]
  rfl
theorem sub30 (p : Pattern) : d30 (change p 10000 (some 80)) = d30 p := by
  change (if p 160 then d2 (change p 10000 (some 80)) else d29 (change p 10000 (some 80))) = d30 p
  rw [sub1, sub29]
  rfl
theorem sub31 (p : Pattern) : d31 (change p 10000 (some 80)) = d31 p := by
  change (if p 159 then d30 (change p 10000 (some 80)) else d4 (change p 10000 (some 80))) = d31 p
  rw [sub30, sub3]
  rfl
theorem sub32 (p : Pattern) : d32 (change p 10000 (some 80)) = d32 p := by
  change (if p 159 then d2 (change p 10000 (some 80)) else d30 (change p 10000 (some 80))) = d32 p
  rw [sub1, sub30]
  rfl
theorem sub33 (p : Pattern) : d33 (change p 10000 (some 80)) = d33 p := by
  change (if p 158 then d32 (change p 10000 (some 80)) else d31 (change p 10000 (some 80))) = d33 p
  rw [sub32, sub31]
  rfl
theorem sub34 (p : Pattern) : d34 (change p 10000 (some 80)) = d34 p := by
  change (if p 139 then d24 (change p 10000 (some 80)) else d33 (change p 10000 (some 80))) = d34 p
  rw [sub24, sub33]
  rfl
theorem sub35 (p : Pattern) : d35 (change p 10000 (some 80)) = d35 p := by
  change (if p 138 then d34 (change p 10000 (some 80)) else d33 (change p 10000 (some 80))) = d35 p
  rw [sub34, sub33]
  rfl
theorem sub36 (p : Pattern) : d36 (change p 10000 (some 80)) = d36 p := by
  change (if p 134 then d35 (change p 10000 (some 80)) else d16 (change p 10000 (some 80))) = d36 p
  rw [sub35, sub16]
  rfl
theorem sub37 (p : Pattern) : d37 (change p 10000 (some 80)) = d37 p := by
  change (if p 159 then d2 (change p 10000 (some 80)) else d5 (change p 10000 (some 80))) = d37 p
  rw [sub1, sub4]
  rfl
theorem sub38 (p : Pattern) : d38 (change p 10000 (some 80)) = d38 p := by
  change (if p 158 then d37 (change p 10000 (some 80)) else d6 (change p 10000 (some 80))) = d38 p
  rw [sub37, sub5]
  rfl
theorem sub39 (p : Pattern) : d39 (change p 10000 (some 80)) = d39 p := by
  change (if p 159 then d2 (change p 10000 (some 80)) else d11 (change p 10000 (some 80))) = d39 p
  rw [sub1, sub11]
  rfl
theorem sub40 (p : Pattern) : d40 (change p 10000 (some 80)) = d40 p := by
  change (if p 158 then d39 (change p 10000 (some 80)) else d12 (change p 10000 (some 80))) = d40 p
  rw [sub39, sub12]
  rfl
theorem sub41 (p : Pattern) : d41 (change p 10000 (some 80)) = d41 p := by
  change (if p 139 then d40 (change p 10000 (some 80)) else d38 (change p 10000 (some 80))) = d41 p
  rw [sub40, sub38]
  rfl
theorem sub42 (p : Pattern) : d42 (change p 10000 (some 80)) = d42 p := by
  change (if p 138 then d41 (change p 10000 (some 80)) else d38 (change p 10000 (some 80))) = d42 p
  rw [sub41, sub38]
  rfl
theorem sub43 (p : Pattern) : d43 (change p 10000 (some 80)) = d43 p := by
  change (if p 134 then d26 (change p 10000 (some 80)) else d42 (change p 10000 (some 80))) = d43 p
  rw [sub26, sub42]
  rfl
theorem sub44 (p : Pattern) : d44 (change p 10000 (some 80)) = d44 p := by
  change (if p 133 then d43 (change p 10000 (some 80)) else d36 (change p 10000 (some 80))) = d44 p
  rw [sub43, sub36]
  rfl
theorem sub45 (p : Pattern) : d45 (change p 10000 (some 80)) = d45 p := by
  change (if p 132 then d44 (change p 10000 (some 80)) else d28 (change p 10000 (some 80))) = d45 p
  rw [sub44, sub28]
  rfl
theorem sub46 (p : Pattern) : d46 (change p 10000 (some 80)) = d46 p := by
  change (if p 134 then d25 (change p 10000 (some 80)) else d15 (change p 10000 (some 80))) = d46 p
  rw [sub25, sub15]
  rfl
theorem sub47 (p : Pattern) : d47 (change p 10000 (some 80)) = d47 p := by
  change (if p 133 then d46 (change p 10000 (some 80)) else d15 (change p 10000 (some 80))) = d47 p
  rw [sub46, sub15]
  rfl
theorem sub48 (p : Pattern) : d48 (change p 10000 (some 80)) = d48 p := by
  change (if p 134 then d34 (change p 10000 (some 80)) else d15 (change p 10000 (some 80))) = d48 p
  rw [sub34, sub15]
  rfl
theorem sub49 (p : Pattern) : d49 (change p 10000 (some 80)) = d49 p := by
  change (if p 134 then d25 (change p 10000 (some 80)) else d41 (change p 10000 (some 80))) = d49 p
  rw [sub25, sub41]
  rfl
theorem sub50 (p : Pattern) : d50 (change p 10000 (some 80)) = d50 p := by
  change (if p 133 then d49 (change p 10000 (some 80)) else d48 (change p 10000 (some 80))) = d50 p
  rw [sub49, sub48]
  rfl
theorem sub51 (p : Pattern) : d51 (change p 10000 (some 80)) = d51 p := by
  change (if p 132 then d50 (change p 10000 (some 80)) else d47 (change p 10000 (some 80))) = d51 p
  rw [sub50, sub47]
  rfl
theorem sub52 (p : Pattern) : d52 (change p 10000 (some 80)) = d52 p := by
  change (if p 139 then d2 (change p 10000 (some 80)) else d8 (change p 10000 (some 80))) = d52 p
  rw [sub1, sub7]
  rfl
theorem sub53 (p : Pattern) : d53 (change p 10000 (some 80)) = d53 p := by
  change (if p 138 then d52 (change p 10000 (some 80)) else d15 (change p 10000 (some 80))) = d53 p
  rw [sub52, sub15]
  rfl
theorem sub54 (p : Pattern) : d54 (change p 10000 (some 80)) = d54 p := by
  change (if p 139 then d2 (change p 10000 (some 80)) else d20 (change p 10000 (some 80))) = d54 p
  rw [sub1, sub20]
  rfl
theorem sub55 (p : Pattern) : d55 (change p 10000 (some 80)) = d55 p := by
  change (if p 138 then d54 (change p 10000 (some 80)) else d25 (change p 10000 (some 80))) = d55 p
  rw [sub54, sub25]
  rfl
theorem sub56 (p : Pattern) : d56 (change p 10000 (some 80)) = d56 p := by
  change (if p 134 then d55 (change p 10000 (some 80)) else d53 (change p 10000 (some 80))) = d56 p
  rw [sub55, sub53]
  rfl
theorem sub57 (p : Pattern) : d57 (change p 10000 (some 80)) = d57 p := by
  change (if p 133 then d56 (change p 10000 (some 80)) else d53 (change p 10000 (some 80))) = d57 p
  rw [sub56, sub53]
  rfl
theorem sub58 (p : Pattern) : d58 (change p 10000 (some 80)) = d58 p := by
  change (if p 139 then d2 (change p 10000 (some 80)) else d33 (change p 10000 (some 80))) = d58 p
  rw [sub1, sub33]
  rfl
theorem sub59 (p : Pattern) : d59 (change p 10000 (some 80)) = d59 p := by
  change (if p 138 then d58 (change p 10000 (some 80)) else d34 (change p 10000 (some 80))) = d59 p
  rw [sub58, sub34]
  rfl
theorem sub60 (p : Pattern) : d60 (change p 10000 (some 80)) = d60 p := by
  change (if p 134 then d59 (change p 10000 (some 80)) else d53 (change p 10000 (some 80))) = d60 p
  rw [sub59, sub53]
  rfl
theorem sub61 (p : Pattern) : d61 (change p 10000 (some 80)) = d61 p := by
  change (if p 139 then d2 (change p 10000 (some 80)) else d38 (change p 10000 (some 80))) = d61 p
  rw [sub1, sub38]
  rfl
theorem sub62 (p : Pattern) : d62 (change p 10000 (some 80)) = d62 p := by
  change (if p 138 then d61 (change p 10000 (some 80)) else d41 (change p 10000 (some 80))) = d62 p
  rw [sub61, sub41]
  rfl
theorem sub63 (p : Pattern) : d63 (change p 10000 (some 80)) = d63 p := by
  change (if p 134 then d55 (change p 10000 (some 80)) else d62 (change p 10000 (some 80))) = d63 p
  rw [sub55, sub62]
  rfl
theorem sub64 (p : Pattern) : d64 (change p 10000 (some 80)) = d64 p := by
  change (if p 133 then d63 (change p 10000 (some 80)) else d60 (change p 10000 (some 80))) = d64 p
  rw [sub63, sub60]
  rfl
theorem sub65 (p : Pattern) : d65 (change p 10000 (some 80)) = d65 p := by
  change (if p 132 then d64 (change p 10000 (some 80)) else d57 (change p 10000 (some 80))) = d65 p
  rw [sub64, sub57]
  rfl
theorem sub66 (p : Pattern) : d66 (change p 10000 (some 80)) = d66 p := by
  change (if p 113 then d65 (change p 10000 (some 80)) else d51 (change p 10000 (some 80))) = d66 p
  rw [sub65, sub51]
  rfl
theorem sub67 (p : Pattern) : d67 (change p 10000 (some 80)) = d67 p := by
  change (if p 112 then d66 (change p 10000 (some 80)) else d45 (change p 10000 (some 80))) = d67 p
  rw [sub66, sub45]
  rfl
theorem sub68 (p : Pattern) : d68 (change p 10000 (some 80)) = d68 p := by
  change (if p 139 then d2 (change p 10000 (some 80)) else d40 (change p 10000 (some 80))) = d68 p
  rw [sub1, sub40]
  rfl
theorem sub69 (p : Pattern) : d70 (change p 10000 (some 80)) = d70 p := by
  change (if p 139 then d2 (change p 10000 (some 80)) else d24 (change p 10000 (some 80))) = d70 p
  rw [sub1, sub24]
  rfl
theorem sub70 (p : Pattern) : d75 (change p 10000 (some 80)) = d75 p := by
  change (if p 134 then d70 (change p 10000 (some 80)) else d68 (change p 10000 (some 80))) = d75 p
  rw [sub69, sub68]
  rfl
theorem sub71 (p : Pattern) : d76 (change p 10000 (some 80)) = d76 p := by
  change (if p 133 then d75 (change p 10000 (some 80)) else d27 (change p 10000 (some 80))) = d76 p
  rw [sub70, sub27]
  rfl
theorem sub72 (p : Pattern) : d77 (change p 10000 (some 80)) = d77 p := by
  change (if p 132 then d76 (change p 10000 (some 80)) else d28 (change p 10000 (some 80))) = d77 p
  rw [sub71, sub28]
  rfl
theorem sub73 (p : Pattern) : d79 (change p 10000 (some 80)) = d79 p := by
  change (if p 133 then d75 (change p 10000 (some 80)) else d46 (change p 10000 (some 80))) = d79 p
  rw [sub70, sub46]
  rfl
theorem sub74 (p : Pattern) : d80 (change p 10000 (some 80)) = d80 p := by
  change (if p 132 then d79 (change p 10000 (some 80)) else d47 (change p 10000 (some 80))) = d80 p
  rw [sub73, sub47]
  rfl
theorem sub75 (p : Pattern) : d81 (change p 10000 (some 80)) = d81 p := by
  change (if p 133 then d75 (change p 10000 (some 80)) else d56 (change p 10000 (some 80))) = d81 p
  rw [sub70, sub56]
  rfl
theorem sub76 (p : Pattern) : d82 (change p 10000 (some 80)) = d82 p := by
  change (if p 132 then d81 (change p 10000 (some 80)) else d57 (change p 10000 (some 80))) = d82 p
  rw [sub75, sub57]
  rfl
theorem sub77 (p : Pattern) : d83 (change p 10000 (some 80)) = d83 p := by
  change (if p 113 then d82 (change p 10000 (some 80)) else d80 (change p 10000 (some 80))) = d83 p
  rw [sub76, sub74]
  rfl
theorem sub78 (p : Pattern) : d117 (change p 10000 (some 80)) = d117 p := by
  change (if p 112 then d83 (change p 10000 (some 80)) else d77 (change p 10000 (some 80))) = d117 p
  rw [sub77, sub72]
  rfl
theorem sub79 (p : Pattern) : d118 (change p 10000 (some 80)) = d118 p := by
  change (if p 106 then d117 (change p 10000 (some 80)) else d67 (change p 10000 (some 80))) = d118 p
  rw [sub78, sub67]
  rfl
theorem sub80 (p : Pattern) : d86 (change p 10000 (some 80)) = d86 p := by
  change (if p 138 then d52 (change p 10000 (some 80)) else d8 (change p 10000 (some 80))) = d86 p
  rw [sub52, sub7]
  rfl
theorem sub81 (p : Pattern) : d87 (change p 10000 (some 80)) = d87 p := by
  change (if p 138 then d54 (change p 10000 (some 80)) else d20 (change p 10000 (some 80))) = d87 p
  rw [sub54, sub20]
  rfl
theorem sub82 (p : Pattern) : d88 (change p 10000 (some 80)) = d88 p := by
  change (if p 134 then d87 (change p 10000 (some 80)) else d86 (change p 10000 (some 80))) = d88 p
  rw [sub81, sub80]
  rfl
theorem sub83 (p : Pattern) : d89 (change p 10000 (some 80)) = d89 p := by
  change (if p 133 then d88 (change p 10000 (some 80)) else d86 (change p 10000 (some 80))) = d89 p
  rw [sub82, sub80]
  rfl
theorem sub84 (p : Pattern) : d119 (change p 10000 (some 80)) = d119 p := by
  change (if p 139 then d20 (change p 10000 (some 80)) else d33 (change p 10000 (some 80))) = d119 p
  rw [sub20, sub33]
  rfl
theorem sub85 (p : Pattern) : d120 (change p 10000 (some 80)) = d120 p := by
  change (if p 138 then d58 (change p 10000 (some 80)) else d119 (change p 10000 (some 80))) = d120 p
  rw [sub58, sub84]
  rfl
theorem sub86 (p : Pattern) : d121 (change p 10000 (some 80)) = d121 p := by
  change (if p 134 then d120 (change p 10000 (some 80)) else d86 (change p 10000 (some 80))) = d121 p
  rw [sub85, sub80]
  rfl
theorem sub87 (p : Pattern) : d92 (change p 10000 (some 80)) = d92 p := by
  change (if p 138 then d61 (change p 10000 (some 80)) else d38 (change p 10000 (some 80))) = d92 p
  rw [sub61, sub38]
  rfl
theorem sub88 (p : Pattern) : d93 (change p 10000 (some 80)) = d93 p := by
  change (if p 134 then d87 (change p 10000 (some 80)) else d92 (change p 10000 (some 80))) = d93 p
  rw [sub81, sub87]
  rfl
theorem sub89 (p : Pattern) : d122 (change p 10000 (some 80)) = d122 p := by
  change (if p 133 then d93 (change p 10000 (some 80)) else d121 (change p 10000 (some 80))) = d122 p
  rw [sub88, sub86]
  rfl
theorem sub90 (p : Pattern) : d123 (change p 10000 (some 80)) = d123 p := by
  change (if p 132 then d122 (change p 10000 (some 80)) else d89 (change p 10000 (some 80))) = d123 p
  rw [sub89, sub83]
  rfl
theorem sub91 (p : Pattern) : d124 (change p 10000 (some 80)) = d124 p := by
  change (if p 113 then d123 (change p 10000 (some 80)) else d45 (change p 10000 (some 80))) = d124 p
  rw [sub90, sub45]
  rfl
theorem sub92 (p : Pattern) : d97 (change p 10000 (some 80)) = d97 p := by
  change (if p 139 then d2 (change p 10000 (some 80)) else d14 (change p 10000 (some 80))) = d97 p
  rw [sub1, sub14]
  rfl
theorem sub93 (p : Pattern) : d98 (change p 10000 (some 80)) = d98 p := by
  change (if p 138 then d97 (change p 10000 (some 80)) else d14 (change p 10000 (some 80))) = d98 p
  rw [sub92, sub14]
  rfl
theorem sub94 (p : Pattern) : d71 (change p 10000 (some 80)) = d71 p := by
  change (if p 138 then d70 (change p 10000 (some 80)) else d24 (change p 10000 (some 80))) = d71 p
  rw [sub69, sub24]
  rfl
theorem sub95 (p : Pattern) : d99 (change p 10000 (some 80)) = d99 p := by
  change (if p 134 then d71 (change p 10000 (some 80)) else d98 (change p 10000 (some 80))) = d99 p
  rw [sub94, sub93]
  rfl
theorem sub96 (p : Pattern) : d100 (change p 10000 (some 80)) = d100 p := by
  change (if p 133 then d99 (change p 10000 (some 80)) else d98 (change p 10000 (some 80))) = d100 p
  rw [sub95, sub93]
  rfl
theorem sub97 (p : Pattern) : d69 (change p 10000 (some 80)) = d69 p := by
  change (if p 138 then d68 (change p 10000 (some 80)) else d40 (change p 10000 (some 80))) = d69 p
  rw [sub68, sub40]
  rfl
theorem sub98 (p : Pattern) : d72 (change p 10000 (some 80)) = d72 p := by
  change (if p 134 then d71 (change p 10000 (some 80)) else d69 (change p 10000 (some 80))) = d72 p
  rw [sub94, sub97]
  rfl
theorem sub99 (p : Pattern) : d101 (change p 10000 (some 80)) = d101 p := by
  change (if p 133 then d72 (change p 10000 (some 80)) else d99 (change p 10000 (some 80))) = d101 p
  rw [sub98, sub95]
  rfl
theorem sub100 (p : Pattern) : d102 (change p 10000 (some 80)) = d102 p := by
  change (if p 132 then d101 (change p 10000 (some 80)) else d100 (change p 10000 (some 80))) = d102 p
  rw [sub99, sub96]
  rfl
theorem sub101 (p : Pattern) : d109 (change p 10000 (some 80)) = d109 p := by
  change (if p 134 then d70 (change p 10000 (some 80)) else d97 (change p 10000 (some 80))) = d109 p
  rw [sub69, sub92]
  rfl
theorem sub102 (p : Pattern) : d110 (change p 10000 (some 80)) = d110 p := by
  change (if p 133 then d109 (change p 10000 (some 80)) else d97 (change p 10000 (some 80))) = d110 p
  rw [sub101, sub92]
  rfl
theorem sub103 (p : Pattern) : d125 (change p 10000 (some 80)) = d125 p := by
  change (if p 133 then d75 (change p 10000 (some 80)) else d109 (change p 10000 (some 80))) = d125 p
  rw [sub70, sub101]
  rfl
theorem sub104 (p : Pattern) : d126 (change p 10000 (some 80)) = d126 p := by
  change (if p 132 then d125 (change p 10000 (some 80)) else d110 (change p 10000 (some 80))) = d126 p
  rw [sub103, sub102]
  rfl
theorem sub105 (p : Pattern) : d127 (change p 10000 (some 80)) = d127 p := by
  change (if p 113 then d126 (change p 10000 (some 80)) else d102 (change p 10000 (some 80))) = d127 p
  rw [sub104, sub100]
  rfl
theorem sub106 (p : Pattern) : d128 (change p 10000 (some 80)) = d128 p := by
  change (if p 112 then d127 (change p 10000 (some 80)) else d124 (change p 10000 (some 80))) = d128 p
  rw [sub105, sub91]
  rfl
theorem sub107 (p : Pattern) : d129 (change p 10000 (some 80)) = d129 p := by
  change (if p 113 then d82 (change p 10000 (some 80)) else d77 (change p 10000 (some 80))) = d129 p
  rw [sub76, sub72]
  rfl
theorem sub108 (p : Pattern) : d111 (change p 10000 (some 80)) = d111 p := by
  change (if p 133 then d2 (change p 10000 (some 80)) else d109 (change p 10000 (some 80))) = d111 p
  rw [sub1, sub101]
  rfl
theorem sub109 (p : Pattern) : d112 (change p 10000 (some 80)) = d112 p := by
  change (if p 132 then d111 (change p 10000 (some 80)) else d110 (change p 10000 (some 80))) = d112 p
  rw [sub108, sub102]
  rfl
theorem sub110 (p : Pattern) : d130 (change p 10000 (some 80)) = d130 p := by
  change (if p 113 then d2 (change p 10000 (some 80)) else d112 (change p 10000 (some 80))) = d130 p
  rw [sub1, sub109]
  rfl
theorem sub111 (p : Pattern) : d131 (change p 10000 (some 80)) = d131 p := by
  change (if p 112 then d130 (change p 10000 (some 80)) else d129 (change p 10000 (some 80))) = d131 p
  rw [sub110, sub107]
  rfl
theorem sub112 (p : Pattern) : d132 (change p 10000 (some 80)) = d132 p := by
  change (if p 106 then d131 (change p 10000 (some 80)) else d128 (change p 10000 (some 80))) = d132 p
  rw [sub111, sub106]
  rfl
theorem sub113 (p : Pattern) : d133 (change p 10000 (some 80)) = d133 p := by
  change (if p 86 then d132 (change p 10000 (some 80)) else d118 (change p 10000 (some 80))) = d133 p
  rw [sub112, sub79]
  rfl
theorem sub114 (p : Pattern) : d134 (change p 10000 (some 80)) = d133 p := by
  change d133 (change p 10000 (some 80)) = d133 p
  exact sub113 p
theorem sub115 (p : Pattern) : d0 (change p 10000 none) = d0 p := by
  rfl
theorem sub116 (p : Pattern) : d2 (change p 10000 none) = d2 p := by
  rfl
theorem sub117 (p : Pattern) : d3 (change p 10000 none) = d3 p := by
  change (if p 161 then d2 (change p 10000 none) else d0 (change p 10000 none)) = d3 p
  rw [sub116, sub115]
  rfl
theorem sub118 (p : Pattern) : d4 (change p 10000 none) = d4 p := by
  change (if p 160 then d3 (change p 10000 none) else d0 (change p 10000 none)) = d4 p
  rw [sub117, sub115]
  rfl
theorem sub119 (p : Pattern) : d5 (change p 10000 none) = d5 p := by
  change (if p 160 then d2 (change p 10000 none) else d0 (change p 10000 none)) = d5 p
  rw [sub116, sub115]
  rfl
end NetHack.Sokoban32Refined
