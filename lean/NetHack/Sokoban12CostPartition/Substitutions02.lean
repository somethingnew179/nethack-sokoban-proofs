/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub240 (p : Pattern) : d279 (change p 141 none) = d179 p := by
  change d179 (change p 141 none) = d179 p
  exact sub239 p
theorem sub241 (p : Pattern) : d280 (change p 141 none) = d180 p := by
  change (if p 134 then d279 (change p 141 none) else d268 (change p 141 none)) = d180 p
  rw [sub240, sub233]
  rfl
theorem sub242 (p : Pattern) : d68 (change p 141 none) = d68 p := by
  change (if p 158 then d55 (change p 141 none) else d57 (change p 141 none)) = d68 p
  rw [sub230, sub232]
  rfl
theorem sub243 (p : Pattern) : d282 (change p 141 none) = d68 p := by
  change d68 (change p 141 none) = d68 p
  exact sub242 p
theorem sub244 (p : Pattern) : d181 (change p 141 none) = d181 p := by
  change (if p 158 then d55 (change p 141 none) else d122 (change p 141 none)) = d181 p
  rw [sub230, sub238]
  rfl
theorem sub245 (p : Pattern) : d284 (change p 141 none) = d181 p := by
  change d181 (change p 141 none) = d181 p
  exact sub244 p
theorem sub246 (p : Pattern) : d285 (change p 141 none) = d182 p := by
  change (if p 134 then d284 (change p 141 none) else d282 (change p 141 none)) = d182 p
  rw [sub245, sub243]
  rfl
theorem sub247 (p : Pattern) : d286 (change p 141 none) = d183 p := by
  change (if p 133 then d285 (change p 141 none) else d280 (change p 141 none)) = d183 p
  rw [sub246, sub241]
  rfl
theorem sub248 (p : Pattern) : d287 (change p 141 none) = d55 p := by
  change d55 (change p 141 none) = d55 p
  exact sub230 p
theorem sub249 (p : Pattern) : d288 (change p 141 none) = d184 p := by
  change (if p 133 then d287 (change p 141 none) else d285 (change p 141 none)) = d184 p
  rw [sub248, sub246]
  rfl
theorem sub250 (p : Pattern) : d289 (change p 141 none) = d185 p := by
  change (if p 132 then d288 (change p 141 none) else d286 (change p 141 none)) = d185 p
  rw [sub249, sub247]
  rfl
theorem sub251 (p : Pattern) : d137 (change p 141 none) = d137 p := by
  change (if p 186 then d55 (change p 141 none) else d119 (change p 141 none)) = d137 p
  rw [sub230, sub235]
  rfl
theorem sub252 (p : Pattern) : d139 (change p 141 none) = d139 p := by
  change (if p 160 then d137 (change p 141 none) else d120 (change p 141 none)) = d139 p
  rw [sub251, sub236]
  rfl
theorem sub253 (p : Pattern) : d153 (change p 141 none) = d153 p := by
  change (if p 159 then d139 (change p 141 none) else d57 (change p 141 none)) = d153 p
  rw [sub252, sub232]
  rfl
theorem sub254 (p : Pattern) : d186 (change p 141 none) = d186 p := by
  change (if p 158 then d153 (change p 141 none) else d57 (change p 141 none)) = d186 p
  rw [sub253, sub232]
  rfl
theorem sub255 (p : Pattern) : d296 (change p 141 none) = d186 p := by
  change d186 (change p 141 none) = d186 p
  exact sub254 p
theorem sub256 (p : Pattern) : d297 (change p 141 none) = d187 p := by
  change (if p 134 then d287 (change p 141 none) else d296 (change p 141 none)) = d187 p
  rw [sub248, sub255]
  rfl
theorem sub257 (p : Pattern) : d138 (change p 141 none) = d138 p := by
  change (if p 160 then d137 (change p 141 none) else d7 (change p 141 none)) = d138 p
  rw [sub251, sub227]
  rfl
theorem sub258 (p : Pattern) : d140 (change p 141 none) = d140 p := by
  change (if p 159 then d139 (change p 141 none) else d138 (change p 141 none)) = d140 p
  rw [sub252, sub257]
  rfl
theorem sub259 (p : Pattern) : d188 (change p 141 none) = d188 p := by
  change (if p 158 then d55 (change p 141 none) else d140 (change p 141 none)) = d188 p
  rw [sub230, sub258]
  rfl
theorem sub260 (p : Pattern) : d301 (change p 141 none) = d188 p := by
  change d188 (change p 141 none) = d188 p
  exact sub259 p
theorem sub261 (p : Pattern) : d302 (change p 141 none) = d189 p := by
  change (if p 134 then d287 (change p 141 none) else d301 (change p 141 none)) = d189 p
  rw [sub248, sub260]
  rfl
theorem sub262 (p : Pattern) : d303 (change p 141 none) = d190 p := by
  change (if p 133 then d302 (change p 141 none) else d297 (change p 141 none)) = d190 p
  rw [sub261, sub256]
  rfl
theorem sub263 (p : Pattern) : d191 (change p 141 none) = d191 p := by
  change (if p 158 then d55 (change p 141 none) else d153 (change p 141 none)) = d191 p
  rw [sub230, sub253]
  rfl
theorem sub264 (p : Pattern) : d305 (change p 141 none) = d191 p := by
  change d191 (change p 141 none) = d191 p
  exact sub263 p
theorem sub265 (p : Pattern) : d306 (change p 141 none) = d192 p := by
  change (if p 134 then d287 (change p 141 none) else d305 (change p 141 none)) = d192 p
  rw [sub248, sub264]
  rfl
theorem sub266 (p : Pattern) : d307 (change p 141 none) = d193 p := by
  change (if p 133 then d287 (change p 141 none) else d306 (change p 141 none)) = d193 p
  rw [sub248, sub265]
  rfl
theorem sub267 (p : Pattern) : d308 (change p 141 none) = d194 p := by
  change (if p 132 then d307 (change p 141 none) else d303 (change p 141 none)) = d194 p
  rw [sub266, sub262]
  rfl
theorem sub268 (p : Pattern) : d309 (change p 141 none) = d195 p := by
  change (if p 108 then d308 (change p 141 none) else d289 (change p 141 none)) = d195 p
  rw [sub267, sub250]
  rfl
theorem sub269 (p : Pattern) : d179 (change p 10000 none) = d179 p := by
  change (if p 158 then d122 (change p 10000 none) else d106 (change p 10000 none)) = d179 p
  rw [sub82, sub66]
  rfl
theorem sub270 (p : Pattern) : d180 (change p 10000 none) = d180 p := by
  change (if p 134 then d179 (change p 10000 none) else d57 (change p 10000 none)) = d180 p
  rw [sub269, sub8]
  rfl
theorem sub271 (p : Pattern) : d181 (change p 10000 none) = d181 p := by
  change (if p 158 then d55 (change p 10000 none) else d122 (change p 10000 none)) = d181 p
  rw [sub6, sub82]
  rfl
theorem sub272 (p : Pattern) : d182 (change p 10000 none) = d182 p := by
  change (if p 134 then d181 (change p 10000 none) else d68 (change p 10000 none)) = d182 p
  rw [sub271, sub27]
  rfl
theorem sub273 (p : Pattern) : d183 (change p 10000 none) = d183 p := by
  change (if p 133 then d182 (change p 10000 none) else d180 (change p 10000 none)) = d183 p
  rw [sub272, sub270]
  rfl
theorem sub274 (p : Pattern) : d184 (change p 10000 none) = d184 p := by
  change (if p 133 then d55 (change p 10000 none) else d182 (change p 10000 none)) = d184 p
  rw [sub6, sub272]
  rfl
theorem sub275 (p : Pattern) : d185 (change p 10000 none) = d185 p := by
  change (if p 132 then d184 (change p 10000 none) else d183 (change p 10000 none)) = d185 p
  rw [sub274, sub273]
  rfl
theorem sub276 (p : Pattern) : d186 (change p 10000 none) = d186 p := by
  change (if p 158 then d153 (change p 10000 none) else d57 (change p 10000 none)) = d186 p
  rw [sub113, sub8]
  rfl
theorem sub277 (p : Pattern) : d187 (change p 10000 none) = d187 p := by
  change (if p 134 then d55 (change p 10000 none) else d186 (change p 10000 none)) = d187 p
  rw [sub6, sub276]
  rfl
theorem sub278 (p : Pattern) : d188 (change p 10000 none) = d188 p := by
  change (if p 158 then d55 (change p 10000 none) else d140 (change p 10000 none)) = d188 p
  rw [sub6, sub100]
  rfl
theorem sub279 (p : Pattern) : d189 (change p 10000 none) = d189 p := by
  change (if p 134 then d55 (change p 10000 none) else d188 (change p 10000 none)) = d189 p
  rw [sub6, sub278]
  rfl
theorem sub280 (p : Pattern) : d190 (change p 10000 none) = d190 p := by
  change (if p 133 then d189 (change p 10000 none) else d187 (change p 10000 none)) = d190 p
  rw [sub279, sub277]
  rfl
theorem sub281 (p : Pattern) : d191 (change p 10000 none) = d191 p := by
  change (if p 158 then d55 (change p 10000 none) else d153 (change p 10000 none)) = d191 p
  rw [sub6, sub113]
  rfl
theorem sub282 (p : Pattern) : d192 (change p 10000 none) = d192 p := by
  change (if p 134 then d55 (change p 10000 none) else d191 (change p 10000 none)) = d192 p
  rw [sub6, sub281]
  rfl
theorem sub283 (p : Pattern) : d193 (change p 10000 none) = d193 p := by
  change (if p 133 then d55 (change p 10000 none) else d192 (change p 10000 none)) = d193 p
  rw [sub6, sub282]
  rfl
theorem sub284 (p : Pattern) : d194 (change p 10000 none) = d194 p := by
  change (if p 132 then d193 (change p 10000 none) else d190 (change p 10000 none)) = d194 p
  rw [sub283, sub280]
  rfl
theorem sub285 (p : Pattern) : d195 (change p 10000 none) = d195 p := by
  change (if p 108 then d194 (change p 10000 none) else d185 (change p 10000 none)) = d195 p
  rw [sub284, sub275]
  rfl
theorem sub286 (p : Pattern) : d0 (change p 10000 (some 168)) = d0 p := by
  rfl
theorem sub287 (p : Pattern) : d2 (change p 10000 (some 168)) = d2 p := by
  rfl
theorem sub288 (p : Pattern) : d6 (change p 10000 (some 168)) = d6 p := by
  change (if p 193 then d2 (change p 10000 (some 168)) else d0 (change p 10000 (some 168))) = d6 p
  rw [sub287, sub286]
  rfl
theorem sub289 (p : Pattern) : d7 (change p 10000 (some 168)) = d7 p := by
  change (if p 192 then d6 (change p 10000 (some 168)) else d0 (change p 10000 (some 168))) = d7 p
  rw [sub288, sub286]
  rfl
theorem sub290 (p : Pattern) : d4 (change p 10000 (some 168)) = d4 p := by
  rfl
theorem sub291 (p : Pattern) : d54 (change p 10000 (some 168)) = d54 p := by
  change (if p 193 then d4 (change p 10000 (some 168)) else d2 (change p 10000 (some 168))) = d54 p
  rw [sub290, sub287]
  rfl
theorem sub292 (p : Pattern) : d55 (change p 10000 (some 168)) = d55 p := by
  change (if p 192 then d54 (change p 10000 (some 168)) else d2 (change p 10000 (some 168))) = d55 p
  rw [sub291, sub287]
  rfl
theorem sub293 (p : Pattern) : d56 (change p 10000 (some 168)) = d56 p := by
  change (if p 186 then d55 (change p 10000 (some 168)) else d7 (change p 10000 (some 168))) = d56 p
  rw [sub292, sub289]
  rfl
theorem sub294 (p : Pattern) : d57 (change p 10000 (some 168)) = d57 p := by
  change (if p 160 then d56 (change p 10000 (some 168)) else d7 (change p 10000 (some 168))) = d57 p
  rw [sub293, sub289]
  rfl
theorem sub295 (p : Pattern) : d106 (change p 10000 (some 168)) = d106 p := by
  change (if p 160 then d55 (change p 10000 (some 168)) else d7 (change p 10000 (some 168))) = d106 p
  rw [sub292, sub289]
  rfl
theorem sub296 (p : Pattern) : d119 (change p 10000 (some 168)) = d119 p := by
  change (if p 187 then d55 (change p 10000 (some 168)) else d7 (change p 10000 (some 168))) = d119 p
  rw [sub292, sub289]
  rfl
theorem sub297 (p : Pattern) : d120 (change p 10000 (some 168)) = d120 p := by
  change (if p 186 then d119 (change p 10000 (some 168)) else d7 (change p 10000 (some 168))) = d120 p
  rw [sub296, sub289]
  rfl
theorem sub298 (p : Pattern) : d121 (change p 10000 (some 168)) = d121 p := by
  change (if p 160 then d55 (change p 10000 (some 168)) else d120 (change p 10000 (some 168))) = d121 p
  rw [sub292, sub297]
  rfl
theorem sub299 (p : Pattern) : d122 (change p 10000 (some 168)) = d122 p := by
  change (if p 159 then d121 (change p 10000 (some 168)) else d106 (change p 10000 (some 168))) = d122 p
  rw [sub298, sub295]
  rfl
theorem sub300 (p : Pattern) : d179 (change p 10000 (some 168)) = d179 p := by
  change (if p 158 then d122 (change p 10000 (some 168)) else d106 (change p 10000 (some 168))) = d179 p
  rw [sub299, sub295]
  rfl
theorem sub301 (p : Pattern) : d180 (change p 10000 (some 168)) = d180 p := by
  change (if p 134 then d179 (change p 10000 (some 168)) else d57 (change p 10000 (some 168))) = d180 p
  rw [sub300, sub294]
  rfl
theorem sub302 (p : Pattern) : d68 (change p 10000 (some 168)) = d68 p := by
  change (if p 158 then d55 (change p 10000 (some 168)) else d57 (change p 10000 (some 168))) = d68 p
  rw [sub292, sub294]
  rfl
theorem sub303 (p : Pattern) : d181 (change p 10000 (some 168)) = d181 p := by
  change (if p 158 then d55 (change p 10000 (some 168)) else d122 (change p 10000 (some 168))) = d181 p
  rw [sub292, sub299]
  rfl
theorem sub304 (p : Pattern) : d182 (change p 10000 (some 168)) = d182 p := by
  change (if p 134 then d181 (change p 10000 (some 168)) else d68 (change p 10000 (some 168))) = d182 p
  rw [sub303, sub302]
  rfl
theorem sub305 (p : Pattern) : d183 (change p 10000 (some 168)) = d183 p := by
  change (if p 133 then d182 (change p 10000 (some 168)) else d180 (change p 10000 (some 168))) = d183 p
  rw [sub304, sub301]
  rfl
theorem sub306 (p : Pattern) : d184 (change p 10000 (some 168)) = d184 p := by
  change (if p 133 then d55 (change p 10000 (some 168)) else d182 (change p 10000 (some 168))) = d184 p
  rw [sub292, sub304]
  rfl
theorem sub307 (p : Pattern) : d185 (change p 10000 (some 168)) = d185 p := by
  change (if p 132 then d184 (change p 10000 (some 168)) else d183 (change p 10000 (some 168))) = d185 p
  rw [sub306, sub305]
  rfl
theorem sub308 (p : Pattern) : d137 (change p 10000 (some 168)) = d137 p := by
  change (if p 186 then d55 (change p 10000 (some 168)) else d119 (change p 10000 (some 168))) = d137 p
  rw [sub292, sub296]
  rfl
theorem sub309 (p : Pattern) : d139 (change p 10000 (some 168)) = d139 p := by
  change (if p 160 then d137 (change p 10000 (some 168)) else d120 (change p 10000 (some 168))) = d139 p
  rw [sub308, sub297]
  rfl
theorem sub310 (p : Pattern) : d153 (change p 10000 (some 168)) = d153 p := by
  change (if p 159 then d139 (change p 10000 (some 168)) else d57 (change p 10000 (some 168))) = d153 p
  rw [sub309, sub294]
  rfl
theorem sub311 (p : Pattern) : d186 (change p 10000 (some 168)) = d186 p := by
  change (if p 158 then d153 (change p 10000 (some 168)) else d57 (change p 10000 (some 168))) = d186 p
  rw [sub310, sub294]
  rfl
theorem sub312 (p : Pattern) : d187 (change p 10000 (some 168)) = d187 p := by
  change (if p 134 then d55 (change p 10000 (some 168)) else d186 (change p 10000 (some 168))) = d187 p
  rw [sub292, sub311]
  rfl
theorem sub313 (p : Pattern) : d138 (change p 10000 (some 168)) = d138 p := by
  change (if p 160 then d137 (change p 10000 (some 168)) else d7 (change p 10000 (some 168))) = d138 p
  rw [sub308, sub289]
  rfl
theorem sub314 (p : Pattern) : d140 (change p 10000 (some 168)) = d140 p := by
  change (if p 159 then d139 (change p 10000 (some 168)) else d138 (change p 10000 (some 168))) = d140 p
  rw [sub309, sub313]
  rfl
theorem sub315 (p : Pattern) : d188 (change p 10000 (some 168)) = d188 p := by
  change (if p 158 then d55 (change p 10000 (some 168)) else d140 (change p 10000 (some 168))) = d188 p
  rw [sub292, sub314]
  rfl
theorem sub316 (p : Pattern) : d189 (change p 10000 (some 168)) = d189 p := by
  change (if p 134 then d55 (change p 10000 (some 168)) else d188 (change p 10000 (some 168))) = d189 p
  rw [sub292, sub315]
  rfl
theorem sub317 (p : Pattern) : d190 (change p 10000 (some 168)) = d190 p := by
  change (if p 133 then d189 (change p 10000 (some 168)) else d187 (change p 10000 (some 168))) = d190 p
  rw [sub316, sub312]
  rfl
theorem sub318 (p : Pattern) : d191 (change p 10000 (some 168)) = d191 p := by
  change (if p 158 then d55 (change p 10000 (some 168)) else d153 (change p 10000 (some 168))) = d191 p
  rw [sub292, sub310]
  rfl
theorem sub319 (p : Pattern) : d192 (change p 10000 (some 168)) = d192 p := by
  change (if p 134 then d55 (change p 10000 (some 168)) else d191 (change p 10000 (some 168))) = d192 p
  rw [sub292, sub318]
  rfl
theorem sub320 (p : Pattern) : d193 (change p 10000 (some 168)) = d193 p := by
  change (if p 133 then d55 (change p 10000 (some 168)) else d192 (change p 10000 (some 168))) = d193 p
  rw [sub292, sub319]
  rfl
theorem sub321 (p : Pattern) : d194 (change p 10000 (some 168)) = d194 p := by
  change (if p 132 then d193 (change p 10000 (some 168)) else d190 (change p 10000 (some 168))) = d194 p
  rw [sub320, sub317]
  rfl
theorem sub322 (p : Pattern) : d195 (change p 10000 (some 168)) = d195 p := by
  change (if p 108 then d194 (change p 10000 (some 168)) else d185 (change p 10000 (some 168))) = d195 p
  rw [sub321, sub307]
  rfl
theorem sub323 (p : Pattern) : d0 (change p 132 (some 133)) = d0 p := by
  rfl
theorem sub324 (p : Pattern) : d2 (change p 132 (some 133)) = d2 p := by
  rfl
theorem sub325 (p : Pattern) : d6 (change p 132 (some 133)) = d6 p := by
  change (if p 193 then d2 (change p 132 (some 133)) else d0 (change p 132 (some 133))) = d6 p
  rw [sub324, sub323]
  rfl
theorem sub326 (p : Pattern) : d7 (change p 132 (some 133)) = d7 p := by
  change (if p 192 then d6 (change p 132 (some 133)) else d0 (change p 132 (some 133))) = d7 p
  rw [sub325, sub323]
  rfl
theorem sub327 (p : Pattern) : d4 (change p 132 (some 133)) = d4 p := by
  rfl
theorem sub328 (p : Pattern) : d54 (change p 132 (some 133)) = d54 p := by
  change (if p 193 then d4 (change p 132 (some 133)) else d2 (change p 132 (some 133))) = d54 p
  rw [sub327, sub324]
  rfl
theorem sub329 (p : Pattern) : d55 (change p 132 (some 133)) = d55 p := by
  change (if p 192 then d54 (change p 132 (some 133)) else d2 (change p 132 (some 133))) = d55 p
  rw [sub328, sub324]
  rfl
theorem sub330 (p : Pattern) : d56 (change p 132 (some 133)) = d56 p := by
  change (if p 186 then d55 (change p 132 (some 133)) else d7 (change p 132 (some 133))) = d56 p
  rw [sub329, sub326]
  rfl
theorem sub331 (p : Pattern) : d57 (change p 132 (some 133)) = d57 p := by
  change (if p 160 then d56 (change p 132 (some 133)) else d7 (change p 132 (some 133))) = d57 p
  rw [sub330, sub326]
  rfl
theorem sub332 (p : Pattern) : d114 (change p 132 (some 133)) = d114 p := by
  change (if p 159 then d55 (change p 132 (some 133)) else d57 (change p 132 (some 133))) = d114 p
  rw [sub329, sub331]
  rfl
theorem sub333 (p : Pattern) : d115 (change p 132 (some 133)) = d115 p := by
  change (if p 158 then d114 (change p 132 (some 133)) else d57 (change p 132 (some 133))) = d115 p
  rw [sub332, sub331]
  rfl
theorem sub334 (p : Pattern) : d1 (change p 132 (some 133)) = d1 p := by
  rfl
theorem sub335 (p : Pattern) : d8 (change p 132 (some 133)) = d8 p := by
  change (if p 271 then d1 (change p 132 (some 133)) else d0 (change p 132 (some 133))) = d8 p
  rw [sub334, sub323]
  rfl
theorem sub336 (p : Pattern) : d3 (change p 132 (some 133)) = d3 p := by
  rfl
theorem sub337 (p : Pattern) : d9 (change p 132 (some 133)) = d9 p := by
  change (if p 271 then d3 (change p 132 (some 133)) else d2 (change p 132 (some 133))) = d9 p
  rw [sub336, sub324]
  rfl
theorem sub338 (p : Pattern) : d10 (change p 132 (some 133)) = d10 p := by
  change (if p 193 then d9 (change p 132 (some 133)) else d8 (change p 132 (some 133))) = d10 p
  rw [sub337, sub335]
  rfl
theorem sub339 (p : Pattern) : d11 (change p 132 (some 133)) = d11 p := by
  change (if p 192 then d10 (change p 132 (some 133)) else d8 (change p 132 (some 133))) = d11 p
  rw [sub338, sub335]
  rfl
theorem sub340 (p : Pattern) : d12 (change p 132 (some 133)) = d12 p := by
  change (if p 168 then d11 (change p 132 (some 133)) else d7 (change p 132 (some 133))) = d12 p
  rw [sub339, sub326]
  rfl
theorem sub341 (p : Pattern) : d5 (change p 132 (some 133)) = d5 p := by
  rfl
theorem sub342 (p : Pattern) : d58 (change p 132 (some 133)) = d58 p := by
  change (if p 271 then d5 (change p 132 (some 133)) else d4 (change p 132 (some 133))) = d58 p
  rw [sub341, sub327]
  rfl
theorem sub343 (p : Pattern) : d59 (change p 132 (some 133)) = d59 p := by
  change (if p 193 then d58 (change p 132 (some 133)) else d9 (change p 132 (some 133))) = d59 p
  rw [sub342, sub337]
  rfl
theorem sub344 (p : Pattern) : d60 (change p 132 (some 133)) = d60 p := by
  change (if p 192 then d59 (change p 132 (some 133)) else d9 (change p 132 (some 133))) = d60 p
  rw [sub343, sub337]
  rfl
theorem sub345 (p : Pattern) : d61 (change p 132 (some 133)) = d61 p := by
  change (if p 186 then d60 (change p 132 (some 133)) else d11 (change p 132 (some 133))) = d61 p
  rw [sub344, sub339]
  rfl
theorem sub346 (p : Pattern) : d62 (change p 132 (some 133)) = d62 p := by
  change (if p 168 then d61 (change p 132 (some 133)) else d56 (change p 132 (some 133))) = d62 p
  rw [sub345, sub330]
  rfl
theorem sub347 (p : Pattern) : d63 (change p 132 (some 133)) = d63 p := by
  change (if p 160 then d62 (change p 132 (some 133)) else d12 (change p 132 (some 133))) = d63 p
  rw [sub346, sub340]
  rfl
theorem sub348 (p : Pattern) : d65 (change p 132 (some 133)) = d65 p := by
  change (if p 168 then d60 (change p 132 (some 133)) else d55 (change p 132 (some 133))) = d65 p
  rw [sub344, sub329]
  rfl
theorem sub349 (p : Pattern) : d116 (change p 132 (some 133)) = d116 p := by
  change (if p 159 then d65 (change p 132 (some 133)) else d63 (change p 132 (some 133))) = d116 p
  rw [sub348, sub347]
  rfl
theorem sub350 (p : Pattern) : d117 (change p 132 (some 133)) = d117 p := by
  change (if p 158 then d116 (change p 132 (some 133)) else d63 (change p 132 (some 133))) = d117 p
  rw [sub349, sub347]
  rfl
theorem sub351 (p : Pattern) : d118 (change p 132 (some 133)) = d118 p := by
  change (if p 141 then d117 (change p 132 (some 133)) else d115 (change p 132 (some 133))) = d118 p
  rw [sub350, sub333]
  rfl
theorem sub352 (p : Pattern) : d106 (change p 132 (some 133)) = d106 p := by
  change (if p 160 then d55 (change p 132 (some 133)) else d7 (change p 132 (some 133))) = d106 p
  rw [sub329, sub326]
  rfl
theorem sub353 (p : Pattern) : d119 (change p 132 (some 133)) = d119 p := by
  change (if p 187 then d55 (change p 132 (some 133)) else d7 (change p 132 (some 133))) = d119 p
  rw [sub329, sub326]
  rfl
theorem sub354 (p : Pattern) : d120 (change p 132 (some 133)) = d120 p := by
  change (if p 186 then d119 (change p 132 (some 133)) else d7 (change p 132 (some 133))) = d120 p
  rw [sub353, sub326]
  rfl
theorem sub355 (p : Pattern) : d121 (change p 132 (some 133)) = d121 p := by
  change (if p 160 then d55 (change p 132 (some 133)) else d120 (change p 132 (some 133))) = d121 p
  rw [sub329, sub354]
  rfl
theorem sub356 (p : Pattern) : d122 (change p 132 (some 133)) = d122 p := by
  change (if p 159 then d121 (change p 132 (some 133)) else d106 (change p 132 (some 133))) = d122 p
  rw [sub355, sub352]
  rfl
theorem sub357 (p : Pattern) : d123 (change p 132 (some 133)) = d123 p := by
  change (if p 159 then d55 (change p 132 (some 133)) else d121 (change p 132 (some 133))) = d123 p
  rw [sub329, sub355]
  rfl
theorem sub358 (p : Pattern) : d124 (change p 132 (some 133)) = d124 p := by
  change (if p 158 then d123 (change p 132 (some 133)) else d122 (change p 132 (some 133))) = d124 p
  rw [sub357, sub356]
  rfl
theorem sub359 (p : Pattern) : d109 (change p 132 (some 133)) = d109 p := by
  change (if p 160 then d65 (change p 132 (some 133)) else d12 (change p 132 (some 133))) = d109 p
  rw [sub348, sub340]
  rfl
end NetHack.Sokoban12CostPartition
