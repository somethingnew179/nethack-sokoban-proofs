/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub240 (p : Pattern) : d125 (change p 10000 none) = d125 p := by
  change (if p 133 then d75 (change p 10000 none) else d109 (change p 10000 none)) = d125 p
  rw [sub190, sub224]
  rfl
theorem sub241 (p : Pattern) : d126 (change p 10000 none) = d126 p := by
  change (if p 132 then d125 (change p 10000 none) else d110 (change p 10000 none)) = d126 p
  rw [sub240, sub225]
  rfl
theorem sub242 (p : Pattern) : d127 (change p 10000 none) = d127 p := by
  change (if p 113 then d126 (change p 10000 none) else d102 (change p 10000 none)) = d127 p
  rw [sub241, sub217]
  rfl
theorem sub243 (p : Pattern) : d128 (change p 10000 none) = d128 p := by
  change (if p 112 then d127 (change p 10000 none) else d124 (change p 10000 none)) = d128 p
  rw [sub242, sub239]
  rfl
theorem sub244 (p : Pattern) : d129 (change p 10000 none) = d129 p := by
  change (if p 113 then d82 (change p 10000 none) else d77 (change p 10000 none)) = d129 p
  rw [sub197, sub192]
  rfl
theorem sub245 (p : Pattern) : d130 (change p 10000 none) = d130 p := by
  change (if p 113 then d2 (change p 10000 none) else d112 (change p 10000 none)) = d130 p
  rw [sub116, sub227]
  rfl
theorem sub246 (p : Pattern) : d131 (change p 10000 none) = d131 p := by
  change (if p 112 then d130 (change p 10000 none) else d129 (change p 10000 none)) = d131 p
  rw [sub245, sub244]
  rfl
theorem sub247 (p : Pattern) : d132 (change p 10000 none) = d132 p := by
  change (if p 106 then d131 (change p 10000 none) else d128 (change p 10000 none)) = d132 p
  rw [sub246, sub243]
  rfl
theorem sub248 (p : Pattern) : d133 (change p 10000 none) = d133 p := by
  change (if p 86 then d132 (change p 10000 none) else d118 (change p 10000 none)) = d133 p
  rw [sub247, sub233]
  rfl
theorem sub249 (p : Pattern) : d134 (change p 10000 none) = d134 p := by
  change (if p 80 then d133 (change p 10000 none) else d116 (change p 10000 none)) = d134 p
  rw [sub248, sub231]
  rfl
theorem sub250 (p : Pattern) : d0 (change p 80 (some 106)) = d0 p := by
  rfl
theorem sub251 (p : Pattern) : d2 (change p 80 (some 106)) = d2 p := by
  rfl
theorem sub252 (p : Pattern) : d3 (change p 80 (some 106)) = d3 p := by
  change (if p 161 then d2 (change p 80 (some 106)) else d0 (change p 80 (some 106))) = d3 p
  rw [sub251, sub250]
  rfl
theorem sub253 (p : Pattern) : d4 (change p 80 (some 106)) = d4 p := by
  change (if p 160 then d3 (change p 80 (some 106)) else d0 (change p 80 (some 106))) = d4 p
  rw [sub252, sub250]
  rfl
theorem sub254 (p : Pattern) : d5 (change p 80 (some 106)) = d5 p := by
  change (if p 160 then d2 (change p 80 (some 106)) else d0 (change p 80 (some 106))) = d5 p
  rw [sub251, sub250]
  rfl
theorem sub255 (p : Pattern) : d6 (change p 80 (some 106)) = d6 p := by
  change (if p 159 then d5 (change p 80 (some 106)) else d4 (change p 80 (some 106))) = d6 p
  rw [sub254, sub253]
  rfl
theorem sub256 (p : Pattern) : d7 (change p 80 (some 106)) = d7 p := by
  change (if p 159 then d2 (change p 80 (some 106)) else d4 (change p 80 (some 106))) = d7 p
  rw [sub251, sub253]
  rfl
theorem sub257 (p : Pattern) : d8 (change p 80 (some 106)) = d8 p := by
  change (if p 158 then d7 (change p 80 (some 106)) else d6 (change p 80 (some 106))) = d8 p
  rw [sub256, sub255]
  rfl
theorem sub258 (p : Pattern) : d1 (change p 80 (some 106)) = d1 p := by
  rfl
theorem sub259 (p : Pattern) : d9 (change p 80 (some 106)) = d9 p := by
  change (if p 161 then d2 (change p 80 (some 106)) else d1 (change p 80 (some 106))) = d9 p
  rw [sub251, sub258]
  rfl
theorem sub260 (p : Pattern) : d10 (change p 80 (some 106)) = d10 p := by
  change (if p 160 then d9 (change p 80 (some 106)) else d1 (change p 80 (some 106))) = d10 p
  rw [sub259, sub258]
  rfl
theorem sub261 (p : Pattern) : d11 (change p 80 (some 106)) = d11 p := by
  change (if p 160 then d2 (change p 80 (some 106)) else d1 (change p 80 (some 106))) = d11 p
  rw [sub251, sub258]
  rfl
theorem sub262 (p : Pattern) : d12 (change p 80 (some 106)) = d12 p := by
  change (if p 159 then d11 (change p 80 (some 106)) else d10 (change p 80 (some 106))) = d12 p
  rw [sub261, sub260]
  rfl
theorem sub263 (p : Pattern) : d13 (change p 80 (some 106)) = d13 p := by
  change (if p 159 then d2 (change p 80 (some 106)) else d10 (change p 80 (some 106))) = d13 p
  rw [sub251, sub260]
  rfl
theorem sub264 (p : Pattern) : d14 (change p 80 (some 106)) = d14 p := by
  change (if p 158 then d13 (change p 80 (some 106)) else d12 (change p 80 (some 106))) = d14 p
  rw [sub263, sub262]
  rfl
theorem sub265 (p : Pattern) : d15 (change p 80 (some 106)) = d15 p := by
  change (if p 139 then d14 (change p 80 (some 106)) else d8 (change p 80 (some 106))) = d15 p
  rw [sub264, sub257]
  rfl
theorem sub266 (p : Pattern) : d16 (change p 80 (some 106)) = d16 p := by
  change (if p 138 then d15 (change p 80 (some 106)) else d8 (change p 80 (some 106))) = d16 p
  rw [sub265, sub257]
  rfl
theorem sub267 (p : Pattern) : d17 (change p 80 (some 106)) = d17 p := by
  change (if p 160 then d2 (change p 80 (some 106)) else d3 (change p 80 (some 106))) = d17 p
  rw [sub251, sub252]
  rfl
theorem sub268 (p : Pattern) : d18 (change p 80 (some 106)) = d18 p := by
  change (if p 159 then d17 (change p 80 (some 106)) else d4 (change p 80 (some 106))) = d18 p
  rw [sub267, sub253]
  rfl
theorem sub269 (p : Pattern) : d19 (change p 80 (some 106)) = d19 p := by
  change (if p 159 then d2 (change p 80 (some 106)) else d17 (change p 80 (some 106))) = d19 p
  rw [sub251, sub267]
  rfl
theorem sub270 (p : Pattern) : d20 (change p 80 (some 106)) = d20 p := by
  change (if p 158 then d19 (change p 80 (some 106)) else d18 (change p 80 (some 106))) = d20 p
  rw [sub269, sub268]
  rfl
theorem sub271 (p : Pattern) : d21 (change p 80 (some 106)) = d21 p := by
  change (if p 160 then d2 (change p 80 (some 106)) else d9 (change p 80 (some 106))) = d21 p
  rw [sub251, sub259]
  rfl
theorem sub272 (p : Pattern) : d22 (change p 80 (some 106)) = d22 p := by
  change (if p 159 then d21 (change p 80 (some 106)) else d10 (change p 80 (some 106))) = d22 p
  rw [sub271, sub260]
  rfl
theorem sub273 (p : Pattern) : d23 (change p 80 (some 106)) = d23 p := by
  change (if p 159 then d2 (change p 80 (some 106)) else d21 (change p 80 (some 106))) = d23 p
  rw [sub251, sub271]
  rfl
theorem sub274 (p : Pattern) : d24 (change p 80 (some 106)) = d24 p := by
  change (if p 158 then d23 (change p 80 (some 106)) else d22 (change p 80 (some 106))) = d24 p
  rw [sub273, sub272]
  rfl
theorem sub275 (p : Pattern) : d25 (change p 80 (some 106)) = d25 p := by
  change (if p 139 then d24 (change p 80 (some 106)) else d20 (change p 80 (some 106))) = d25 p
  rw [sub274, sub270]
  rfl
theorem sub276 (p : Pattern) : d26 (change p 80 (some 106)) = d26 p := by
  change (if p 138 then d25 (change p 80 (some 106)) else d20 (change p 80 (some 106))) = d26 p
  rw [sub275, sub270]
  rfl
theorem sub277 (p : Pattern) : d27 (change p 80 (some 106)) = d27 p := by
  change (if p 134 then d26 (change p 80 (some 106)) else d16 (change p 80 (some 106))) = d27 p
  rw [sub276, sub266]
  rfl
theorem sub278 (p : Pattern) : d28 (change p 80 (some 106)) = d28 p := by
  change (if p 133 then d27 (change p 80 (some 106)) else d16 (change p 80 (some 106))) = d28 p
  rw [sub277, sub266]
  rfl
theorem sub279 (p : Pattern) : d39 (change p 80 (some 106)) = d39 p := by
  change (if p 159 then d2 (change p 80 (some 106)) else d11 (change p 80 (some 106))) = d39 p
  rw [sub251, sub261]
  rfl
theorem sub280 (p : Pattern) : d40 (change p 80 (some 106)) = d40 p := by
  change (if p 158 then d39 (change p 80 (some 106)) else d12 (change p 80 (some 106))) = d40 p
  rw [sub279, sub262]
  rfl
theorem sub281 (p : Pattern) : d68 (change p 80 (some 106)) = d68 p := by
  change (if p 139 then d2 (change p 80 (some 106)) else d40 (change p 80 (some 106))) = d68 p
  rw [sub251, sub280]
  rfl
theorem sub282 (p : Pattern) : d69 (change p 80 (some 106)) = d69 p := by
  change (if p 138 then d68 (change p 80 (some 106)) else d40 (change p 80 (some 106))) = d69 p
  rw [sub281, sub280]
  rfl
theorem sub283 (p : Pattern) : d70 (change p 80 (some 106)) = d70 p := by
  change (if p 139 then d2 (change p 80 (some 106)) else d24 (change p 80 (some 106))) = d70 p
  rw [sub251, sub274]
  rfl
theorem sub284 (p : Pattern) : d71 (change p 80 (some 106)) = d71 p := by
  change (if p 138 then d70 (change p 80 (some 106)) else d24 (change p 80 (some 106))) = d71 p
  rw [sub283, sub274]
  rfl
theorem sub285 (p : Pattern) : d72 (change p 80 (some 106)) = d72 p := by
  change (if p 134 then d71 (change p 80 (some 106)) else d69 (change p 80 (some 106))) = d72 p
  rw [sub284, sub282]
  rfl
theorem sub286 (p : Pattern) : d73 (change p 80 (some 106)) = d73 p := by
  change (if p 133 then d72 (change p 80 (some 106)) else d27 (change p 80 (some 106))) = d73 p
  rw [sub285, sub277]
  rfl
theorem sub287 (p : Pattern) : d74 (change p 80 (some 106)) = d74 p := by
  change (if p 132 then d73 (change p 80 (some 106)) else d28 (change p 80 (some 106))) = d74 p
  rw [sub286, sub278]
  rfl
theorem sub288 (p : Pattern) : d75 (change p 80 (some 106)) = d75 p := by
  change (if p 134 then d70 (change p 80 (some 106)) else d68 (change p 80 (some 106))) = d75 p
  rw [sub283, sub281]
  rfl
theorem sub289 (p : Pattern) : d76 (change p 80 (some 106)) = d76 p := by
  change (if p 133 then d75 (change p 80 (some 106)) else d27 (change p 80 (some 106))) = d76 p
  rw [sub288, sub277]
  rfl
theorem sub290 (p : Pattern) : d77 (change p 80 (some 106)) = d77 p := by
  change (if p 132 then d76 (change p 80 (some 106)) else d28 (change p 80 (some 106))) = d77 p
  rw [sub289, sub278]
  rfl
theorem sub291 (p : Pattern) : d78 (change p 80 (some 106)) = d78 p := by
  change (if p 113 then d77 (change p 80 (some 106)) else d74 (change p 80 (some 106))) = d78 p
  rw [sub290, sub287]
  rfl
theorem sub292 (p : Pattern) : d46 (change p 80 (some 106)) = d46 p := by
  change (if p 134 then d25 (change p 80 (some 106)) else d15 (change p 80 (some 106))) = d46 p
  rw [sub275, sub265]
  rfl
theorem sub293 (p : Pattern) : d47 (change p 80 (some 106)) = d47 p := by
  change (if p 133 then d46 (change p 80 (some 106)) else d15 (change p 80 (some 106))) = d47 p
  rw [sub292, sub265]
  rfl
theorem sub294 (p : Pattern) : d79 (change p 80 (some 106)) = d79 p := by
  change (if p 133 then d75 (change p 80 (some 106)) else d46 (change p 80 (some 106))) = d79 p
  rw [sub288, sub292]
  rfl
theorem sub295 (p : Pattern) : d80 (change p 80 (some 106)) = d80 p := by
  change (if p 132 then d79 (change p 80 (some 106)) else d47 (change p 80 (some 106))) = d80 p
  rw [sub294, sub293]
  rfl
theorem sub296 (p : Pattern) : d52 (change p 80 (some 106)) = d52 p := by
  change (if p 139 then d2 (change p 80 (some 106)) else d8 (change p 80 (some 106))) = d52 p
  rw [sub251, sub257]
  rfl
theorem sub297 (p : Pattern) : d53 (change p 80 (some 106)) = d53 p := by
  change (if p 138 then d52 (change p 80 (some 106)) else d15 (change p 80 (some 106))) = d53 p
  rw [sub296, sub265]
  rfl
theorem sub298 (p : Pattern) : d54 (change p 80 (some 106)) = d54 p := by
  change (if p 139 then d2 (change p 80 (some 106)) else d20 (change p 80 (some 106))) = d54 p
  rw [sub251, sub270]
  rfl
theorem sub299 (p : Pattern) : d55 (change p 80 (some 106)) = d55 p := by
  change (if p 138 then d54 (change p 80 (some 106)) else d25 (change p 80 (some 106))) = d55 p
  rw [sub298, sub275]
  rfl
theorem sub300 (p : Pattern) : d56 (change p 80 (some 106)) = d56 p := by
  change (if p 134 then d55 (change p 80 (some 106)) else d53 (change p 80 (some 106))) = d56 p
  rw [sub299, sub297]
  rfl
theorem sub301 (p : Pattern) : d57 (change p 80 (some 106)) = d57 p := by
  change (if p 133 then d56 (change p 80 (some 106)) else d53 (change p 80 (some 106))) = d57 p
  rw [sub300, sub297]
  rfl
theorem sub302 (p : Pattern) : d81 (change p 80 (some 106)) = d81 p := by
  change (if p 133 then d75 (change p 80 (some 106)) else d56 (change p 80 (some 106))) = d81 p
  rw [sub288, sub300]
  rfl
theorem sub303 (p : Pattern) : d82 (change p 80 (some 106)) = d82 p := by
  change (if p 132 then d81 (change p 80 (some 106)) else d57 (change p 80 (some 106))) = d82 p
  rw [sub302, sub301]
  rfl
theorem sub304 (p : Pattern) : d83 (change p 80 (some 106)) = d83 p := by
  change (if p 113 then d82 (change p 80 (some 106)) else d80 (change p 80 (some 106))) = d83 p
  rw [sub303, sub295]
  rfl
theorem sub305 (p : Pattern) : d84 (change p 80 (some 106)) = d84 p := by
  change (if p 112 then d83 (change p 80 (some 106)) else d78 (change p 80 (some 106))) = d84 p
  rw [sub304, sub291]
  rfl
theorem sub306 (p : Pattern) : d85 (change p 80 (some 106)) = d84 p := by
  change d84 (change p 80 (some 106)) = d84 p
  exact sub305 p
theorem sub307 (p : Pattern) : d86 (change p 80 (some 106)) = d86 p := by
  change (if p 138 then d52 (change p 80 (some 106)) else d8 (change p 80 (some 106))) = d86 p
  rw [sub296, sub257]
  rfl
theorem sub308 (p : Pattern) : d87 (change p 80 (some 106)) = d87 p := by
  change (if p 138 then d54 (change p 80 (some 106)) else d20 (change p 80 (some 106))) = d87 p
  rw [sub298, sub270]
  rfl
theorem sub309 (p : Pattern) : d88 (change p 80 (some 106)) = d88 p := by
  change (if p 134 then d87 (change p 80 (some 106)) else d86 (change p 80 (some 106))) = d88 p
  rw [sub308, sub307]
  rfl
theorem sub310 (p : Pattern) : d89 (change p 80 (some 106)) = d89 p := by
  change (if p 133 then d88 (change p 80 (some 106)) else d86 (change p 80 (some 106))) = d89 p
  rw [sub309, sub307]
  rfl
theorem sub311 (p : Pattern) : d104 (change p 80 (some 106)) = d104 p := by
  change (if p 133 then d75 (change p 80 (some 106)) else d88 (change p 80 (some 106))) = d104 p
  rw [sub288, sub309]
  rfl
theorem sub312 (p : Pattern) : d105 (change p 80 (some 106)) = d105 p := by
  change (if p 132 then d104 (change p 80 (some 106)) else d89 (change p 80 (some 106))) = d105 p
  rw [sub311, sub310]
  rfl
theorem sub313 (p : Pattern) : d106 (change p 80 (some 106)) = d106 p := by
  change (if p 113 then d105 (change p 80 (some 106)) else d77 (change p 80 (some 106))) = d106 p
  rw [sub312, sub290]
  rfl
theorem sub314 (p : Pattern) : d97 (change p 80 (some 106)) = d97 p := by
  change (if p 139 then d2 (change p 80 (some 106)) else d14 (change p 80 (some 106))) = d97 p
  rw [sub251, sub264]
  rfl
theorem sub315 (p : Pattern) : d98 (change p 80 (some 106)) = d98 p := by
  change (if p 138 then d97 (change p 80 (some 106)) else d14 (change p 80 (some 106))) = d98 p
  rw [sub314, sub264]
  rfl
theorem sub316 (p : Pattern) : d99 (change p 80 (some 106)) = d99 p := by
  change (if p 134 then d71 (change p 80 (some 106)) else d98 (change p 80 (some 106))) = d99 p
  rw [sub284, sub315]
  rfl
theorem sub317 (p : Pattern) : d100 (change p 80 (some 106)) = d100 p := by
  change (if p 133 then d99 (change p 80 (some 106)) else d98 (change p 80 (some 106))) = d100 p
  rw [sub316, sub315]
  rfl
theorem sub318 (p : Pattern) : d107 (change p 80 (some 106)) = d107 p := by
  change (if p 133 then d2 (change p 80 (some 106)) else d99 (change p 80 (some 106))) = d107 p
  rw [sub251, sub316]
  rfl
theorem sub319 (p : Pattern) : d108 (change p 80 (some 106)) = d108 p := by
  change (if p 132 then d107 (change p 80 (some 106)) else d100 (change p 80 (some 106))) = d108 p
  rw [sub318, sub317]
  rfl
theorem sub320 (p : Pattern) : d109 (change p 80 (some 106)) = d109 p := by
  change (if p 134 then d70 (change p 80 (some 106)) else d97 (change p 80 (some 106))) = d109 p
  rw [sub283, sub314]
  rfl
theorem sub321 (p : Pattern) : d110 (change p 80 (some 106)) = d110 p := by
  change (if p 133 then d109 (change p 80 (some 106)) else d97 (change p 80 (some 106))) = d110 p
  rw [sub320, sub314]
  rfl
theorem sub322 (p : Pattern) : d111 (change p 80 (some 106)) = d111 p := by
  change (if p 133 then d2 (change p 80 (some 106)) else d109 (change p 80 (some 106))) = d111 p
  rw [sub251, sub320]
  rfl
theorem sub323 (p : Pattern) : d112 (change p 80 (some 106)) = d112 p := by
  change (if p 132 then d111 (change p 80 (some 106)) else d110 (change p 80 (some 106))) = d112 p
  rw [sub322, sub321]
  rfl
theorem sub324 (p : Pattern) : d113 (change p 80 (some 106)) = d113 p := by
  change (if p 113 then d112 (change p 80 (some 106)) else d108 (change p 80 (some 106))) = d113 p
  rw [sub323, sub319]
  rfl
theorem sub325 (p : Pattern) : d114 (change p 80 (some 106)) = d114 p := by
  change (if p 112 then d113 (change p 80 (some 106)) else d106 (change p 80 (some 106))) = d114 p
  rw [sub324, sub313]
  rfl
theorem sub326 (p : Pattern) : d115 (change p 80 (some 106)) = d114 p := by
  change d114 (change p 80 (some 106)) = d114 p
  exact sub325 p
theorem sub327 (p : Pattern) : d116 (change p 80 (some 106)) = d831 p := by
  change (if p 86 then d115 (change p 80 (some 106)) else d85 (change p 80 (some 106))) = d831 p
  rw [sub326, sub306]
  rfl
theorem sub328 (p : Pattern) : d173 (change p 80 (some 106)) = d831 p := by
  change d116 (change p 80 (some 106)) = d831 p
  exact sub327 p
theorem sub329 (p : Pattern) : d0 (change p 86 (some 112)) = d0 p := by
  rfl
theorem sub330 (p : Pattern) : d2 (change p 86 (some 112)) = d2 p := by
  rfl
theorem sub331 (p : Pattern) : d3 (change p 86 (some 112)) = d3 p := by
  change (if p 161 then d2 (change p 86 (some 112)) else d0 (change p 86 (some 112))) = d3 p
  rw [sub330, sub329]
  rfl
theorem sub332 (p : Pattern) : d4 (change p 86 (some 112)) = d4 p := by
  change (if p 160 then d3 (change p 86 (some 112)) else d0 (change p 86 (some 112))) = d4 p
  rw [sub331, sub329]
  rfl
theorem sub333 (p : Pattern) : d5 (change p 86 (some 112)) = d5 p := by
  change (if p 160 then d2 (change p 86 (some 112)) else d0 (change p 86 (some 112))) = d5 p
  rw [sub330, sub329]
  rfl
theorem sub334 (p : Pattern) : d6 (change p 86 (some 112)) = d6 p := by
  change (if p 159 then d5 (change p 86 (some 112)) else d4 (change p 86 (some 112))) = d6 p
  rw [sub333, sub332]
  rfl
theorem sub335 (p : Pattern) : d7 (change p 86 (some 112)) = d7 p := by
  change (if p 159 then d2 (change p 86 (some 112)) else d4 (change p 86 (some 112))) = d7 p
  rw [sub330, sub332]
  rfl
theorem sub336 (p : Pattern) : d8 (change p 86 (some 112)) = d8 p := by
  change (if p 158 then d7 (change p 86 (some 112)) else d6 (change p 86 (some 112))) = d8 p
  rw [sub335, sub334]
  rfl
theorem sub337 (p : Pattern) : d1 (change p 86 (some 112)) = d1 p := by
  rfl
theorem sub338 (p : Pattern) : d9 (change p 86 (some 112)) = d9 p := by
  change (if p 161 then d2 (change p 86 (some 112)) else d1 (change p 86 (some 112))) = d9 p
  rw [sub330, sub337]
  rfl
theorem sub339 (p : Pattern) : d10 (change p 86 (some 112)) = d10 p := by
  change (if p 160 then d9 (change p 86 (some 112)) else d1 (change p 86 (some 112))) = d10 p
  rw [sub338, sub337]
  rfl
theorem sub340 (p : Pattern) : d11 (change p 86 (some 112)) = d11 p := by
  change (if p 160 then d2 (change p 86 (some 112)) else d1 (change p 86 (some 112))) = d11 p
  rw [sub330, sub337]
  rfl
theorem sub341 (p : Pattern) : d12 (change p 86 (some 112)) = d12 p := by
  change (if p 159 then d11 (change p 86 (some 112)) else d10 (change p 86 (some 112))) = d12 p
  rw [sub340, sub339]
  rfl
theorem sub342 (p : Pattern) : d13 (change p 86 (some 112)) = d13 p := by
  change (if p 159 then d2 (change p 86 (some 112)) else d10 (change p 86 (some 112))) = d13 p
  rw [sub330, sub339]
  rfl
theorem sub343 (p : Pattern) : d14 (change p 86 (some 112)) = d14 p := by
  change (if p 158 then d13 (change p 86 (some 112)) else d12 (change p 86 (some 112))) = d14 p
  rw [sub342, sub341]
  rfl
theorem sub344 (p : Pattern) : d15 (change p 86 (some 112)) = d15 p := by
  change (if p 139 then d14 (change p 86 (some 112)) else d8 (change p 86 (some 112))) = d15 p
  rw [sub343, sub336]
  rfl
theorem sub345 (p : Pattern) : d17 (change p 86 (some 112)) = d17 p := by
  change (if p 160 then d2 (change p 86 (some 112)) else d3 (change p 86 (some 112))) = d17 p
  rw [sub330, sub331]
  rfl
theorem sub346 (p : Pattern) : d18 (change p 86 (some 112)) = d18 p := by
  change (if p 159 then d17 (change p 86 (some 112)) else d4 (change p 86 (some 112))) = d18 p
  rw [sub345, sub332]
  rfl
theorem sub347 (p : Pattern) : d19 (change p 86 (some 112)) = d19 p := by
  change (if p 159 then d2 (change p 86 (some 112)) else d17 (change p 86 (some 112))) = d19 p
  rw [sub330, sub345]
  rfl
theorem sub348 (p : Pattern) : d20 (change p 86 (some 112)) = d20 p := by
  change (if p 158 then d19 (change p 86 (some 112)) else d18 (change p 86 (some 112))) = d20 p
  rw [sub347, sub346]
  rfl
theorem sub349 (p : Pattern) : d21 (change p 86 (some 112)) = d21 p := by
  change (if p 160 then d2 (change p 86 (some 112)) else d9 (change p 86 (some 112))) = d21 p
  rw [sub330, sub338]
  rfl
theorem sub350 (p : Pattern) : d22 (change p 86 (some 112)) = d22 p := by
  change (if p 159 then d21 (change p 86 (some 112)) else d10 (change p 86 (some 112))) = d22 p
  rw [sub349, sub339]
  rfl
theorem sub351 (p : Pattern) : d23 (change p 86 (some 112)) = d23 p := by
  change (if p 159 then d2 (change p 86 (some 112)) else d21 (change p 86 (some 112))) = d23 p
  rw [sub330, sub349]
  rfl
theorem sub352 (p : Pattern) : d24 (change p 86 (some 112)) = d24 p := by
  change (if p 158 then d23 (change p 86 (some 112)) else d22 (change p 86 (some 112))) = d24 p
  rw [sub351, sub350]
  rfl
theorem sub353 (p : Pattern) : d25 (change p 86 (some 112)) = d25 p := by
  change (if p 139 then d24 (change p 86 (some 112)) else d20 (change p 86 (some 112))) = d25 p
  rw [sub352, sub348]
  rfl
theorem sub354 (p : Pattern) : d46 (change p 86 (some 112)) = d46 p := by
  change (if p 134 then d25 (change p 86 (some 112)) else d15 (change p 86 (some 112))) = d46 p
  rw [sub353, sub344]
  rfl
theorem sub355 (p : Pattern) : d47 (change p 86 (some 112)) = d47 p := by
  change (if p 133 then d46 (change p 86 (some 112)) else d15 (change p 86 (some 112))) = d47 p
  rw [sub354, sub344]
  rfl
theorem sub356 (p : Pattern) : d29 (change p 86 (some 112)) = d29 p := by
  change (if p 161 then d1 (change p 86 (some 112)) else d0 (change p 86 (some 112))) = d29 p
  rw [sub337, sub329]
  rfl
theorem sub357 (p : Pattern) : d30 (change p 86 (some 112)) = d30 p := by
  change (if p 160 then d2 (change p 86 (some 112)) else d29 (change p 86 (some 112))) = d30 p
  rw [sub330, sub356]
  rfl
theorem sub358 (p : Pattern) : d31 (change p 86 (some 112)) = d31 p := by
  change (if p 159 then d30 (change p 86 (some 112)) else d4 (change p 86 (some 112))) = d31 p
  rw [sub357, sub332]
  rfl
theorem sub359 (p : Pattern) : d32 (change p 86 (some 112)) = d32 p := by
  change (if p 159 then d2 (change p 86 (some 112)) else d30 (change p 86 (some 112))) = d32 p
  rw [sub330, sub357]
  rfl
end NetHack.Sokoban32Refined
