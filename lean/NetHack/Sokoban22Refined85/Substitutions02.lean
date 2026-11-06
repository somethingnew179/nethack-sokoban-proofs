/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub240 (p : Pattern) : d240 (change p 10000 none) = d240 p := by
  change (if p 141 then d239 (change p 10000 none) else d233 (change p 10000 none)) = d240 p
  rw [sub239, sub233]
  rfl
theorem sub241 (p : Pattern) : d241 (change p 10000 none) = d241 p := by
  change (if p 163 then d62 (change p 10000 none) else d132 (change p 10000 none)) = d241 p
  rw [sub57, sub131]
  rfl
theorem sub242 (p : Pattern) : d242 (change p 10000 none) = d242 p := by
  change (if p 162 then d241 (change p 10000 none) else d105 (change p 10000 none)) = d242 p
  rw [sub241, sub101]
  rfl
theorem sub243 (p : Pattern) : d243 (change p 10000 none) = d243 p := by
  change (if p 161 then d137 (change p 10000 none) else d242 (change p 10000 none)) = d243 p
  rw [sub136, sub242]
  rfl
theorem sub244 (p : Pattern) : d244 (change p 10000 none) = d244 p := by
  change (if p 160 then d155 (change p 10000 none) else d243 (change p 10000 none)) = d244 p
  rw [sub154, sub243]
  rfl
theorem sub245 (p : Pattern) : d245 (change p 10000 none) = d245 p := by
  change (if p 162 then d211 (change p 10000 none) else d132 (change p 10000 none)) = d245 p
  rw [sub211, sub131]
  rfl
theorem sub246 (p : Pattern) : d246 (change p 10000 none) = d246 p := by
  change (if p 161 then d154 (change p 10000 none) else d245 (change p 10000 none)) = d246 p
  rw [sub153, sub245]
  rfl
theorem sub247 (p : Pattern) : d247 (change p 10000 none) = d247 p := by
  change (if p 162 then d12 (change p 10000 none) else d27 (change p 10000 none)) = d247 p
  rw [sub1, sub18]
  rfl
theorem sub248 (p : Pattern) : d248 (change p 10000 none) = d248 p := by
  change (if p 161 then d12 (change p 10000 none) else d247 (change p 10000 none)) = d248 p
  rw [sub1, sub247]
  rfl
theorem sub249 (p : Pattern) : d249 (change p 10000 none) = d249 p := by
  change (if p 160 then d248 (change p 10000 none) else d246 (change p 10000 none)) = d249 p
  rw [sub248, sub246]
  rfl
theorem sub250 (p : Pattern) : d250 (change p 10000 none) = d250 p := by
  change (if p 141 then d249 (change p 10000 none) else d244 (change p 10000 none)) = d250 p
  rw [sub249, sub244]
  rfl
theorem sub251 (p : Pattern) : d251 (change p 10000 none) = d251 p := by
  change (if p 138 then d250 (change p 10000 none) else d240 (change p 10000 none)) = d251 p
  rw [sub250, sub240]
  rfl
theorem sub252 (p : Pattern) : d252 (change p 10000 none) = d252 p := by
  change (if p 163 then d26 (change p 10000 none) else d132 (change p 10000 none)) = d252 p
  rw [sub17, sub131]
  rfl
theorem sub253 (p : Pattern) : d253 (change p 10000 none) = d253 p := by
  change (if p 162 then d252 (change p 10000 none) else d105 (change p 10000 none)) = d253 p
  rw [sub252, sub101]
  rfl
theorem sub254 (p : Pattern) : d254 (change p 10000 none) = d254 p := by
  change (if p 163 then d26 (change p 10000 none) else d109 (change p 10000 none)) = d254 p
  rw [sub17, sub106]
  rfl
theorem sub255 (p : Pattern) : d255 (change p 10000 none) = d255 p := by
  change (if p 162 then d12 (change p 10000 none) else d254 (change p 10000 none)) = d255 p
  rw [sub1, sub254]
  rfl
theorem sub256 (p : Pattern) : d256 (change p 10000 none) = d256 p := by
  change (if p 161 then d255 (change p 10000 none) else d253 (change p 10000 none)) = d256 p
  rw [sub255, sub253]
  rfl
theorem sub257 (p : Pattern) : d257 (change p 10000 none) = d257 p := by
  change (if p 163 then d62 (change p 10000 none) else d148 (change p 10000 none)) = d257 p
  rw [sub57, sub147]
  rfl
theorem sub258 (p : Pattern) : d258 (change p 10000 none) = d258 p := by
  change (if p 162 then d12 (change p 10000 none) else d257 (change p 10000 none)) = d258 p
  rw [sub1, sub257]
  rfl
theorem sub259 (p : Pattern) : d259 (change p 10000 none) = d259 p := by
  change (if p 161 then d12 (change p 10000 none) else d258 (change p 10000 none)) = d259 p
  rw [sub1, sub258]
  rfl
theorem sub260 (p : Pattern) : d260 (change p 10000 none) = d260 p := by
  change (if p 160 then d259 (change p 10000 none) else d256 (change p 10000 none)) = d260 p
  rw [sub259, sub256]
  rfl
theorem sub261 (p : Pattern) : d261 (change p 10000 none) = d261 p := by
  change (if p 141 then d249 (change p 10000 none) else d260 (change p 10000 none)) = d261 p
  rw [sub249, sub260]
  rfl
theorem sub262 (p : Pattern) : d262 (change p 10000 none) = d262 p := by
  change (if p 138 then d12 (change p 10000 none) else d261 (change p 10000 none)) = d262 p
  rw [sub1, sub261]
  rfl
theorem sub263 (p : Pattern) : d263 (change p 10000 none) = d263 p := by
  change (if p 116 then d262 (change p 10000 none) else d251 (change p 10000 none)) = d263 p
  rw [sub262, sub251]
  rfl
theorem sub264 (p : Pattern) : d264 (change p 10000 none) = d264 p := by
  change (if p 115 then d263 (change p 10000 none) else d225 (change p 10000 none)) = d264 p
  rw [sub263, sub225]
  rfl
theorem sub265 (p : Pattern) : d265 (change p 10000 none) = d265 p := by
  change (if p 71 then d264 (change p 10000 none) else d101 (change p 10000 none)) = d265 p
  rw [sub264, sub96]
  rfl
theorem sub266 (p : Pattern) : d266 (change p 10000 none) = d266 p := by
  change (if p 49 then d265 (change p 10000 none) else d210 (change p 10000 none)) = d266 p
  rw [sub265, sub210]
  rfl
theorem sub267 (p : Pattern) : d267 (change p 10000 none) = d267 p := by
  change (if p 48 then d266 (change p 10000 none) else d169 (change p 10000 none)) = d267 p
  rw [sub266, sub168]
  rfl
theorem sub268 (p : Pattern) : d0 (change p 49 (some 71)) = d0 p := by
  rfl
theorem sub269 (p : Pattern) : d12 (change p 49 (some 71)) = d12 p := by
  rfl
theorem sub270 (p : Pattern) : d13 (change p 49 (some 71)) = d13 p := by
  change (if p 247 then d12 (change p 49 (some 71)) else d0 (change p 49 (some 71))) = d13 p
  rw [sub269, sub268]
  rfl
theorem sub271 (p : Pattern) : d14 (change p 49 (some 71)) = d14 p := by
  change (if p 246 then d13 (change p 49 (some 71)) else d0 (change p 49 (some 71))) = d14 p
  rw [sub270, sub268]
  rfl
theorem sub272 (p : Pattern) : d15 (change p 49 (some 71)) = d15 p := by
  change (if p 204 then d12 (change p 49 (some 71)) else d14 (change p 49 (some 71))) = d15 p
  rw [sub269, sub271]
  rfl
theorem sub273 (p : Pattern) : d16 (change p 49 (some 71)) = d16 p := by
  change (if p 182 then d15 (change p 49 (some 71)) else d14 (change p 49 (some 71))) = d16 p
  rw [sub272, sub271]
  rfl
theorem sub274 (p : Pattern) : d4 (change p 49 (some 71)) = d4 p := by
  rfl
theorem sub275 (p : Pattern) : d17 (change p 49 (some 71)) = d17 p := by
  change (if p 247 then d12 (change p 49 (some 71)) else d4 (change p 49 (some 71))) = d17 p
  rw [sub269, sub274]
  rfl
theorem sub276 (p : Pattern) : d18 (change p 49 (some 71)) = d18 p := by
  change (if p 246 then d17 (change p 49 (some 71)) else d4 (change p 49 (some 71))) = d18 p
  rw [sub275, sub274]
  rfl
theorem sub277 (p : Pattern) : d19 (change p 49 (some 71)) = d19 p := by
  change (if p 204 then d12 (change p 49 (some 71)) else d18 (change p 49 (some 71))) = d19 p
  rw [sub269, sub276]
  rfl
theorem sub278 (p : Pattern) : d20 (change p 49 (some 71)) = d20 p := by
  change (if p 182 then d19 (change p 49 (some 71)) else d18 (change p 49 (some 71))) = d20 p
  rw [sub277, sub276]
  rfl
theorem sub279 (p : Pattern) : d21 (change p 49 (some 71)) = d21 p := by
  change (if p 163 then d20 (change p 49 (some 71)) else d16 (change p 49 (some 71))) = d21 p
  rw [sub278, sub273]
  rfl
theorem sub280 (p : Pattern) : d22 (change p 49 (some 71)) = d22 p := by
  change (if p 162 then d21 (change p 49 (some 71)) else d16 (change p 49 (some 71))) = d22 p
  rw [sub279, sub273]
  rfl
theorem sub281 (p : Pattern) : d9 (change p 49 (some 71)) = d9 p := by
  rfl
theorem sub282 (p : Pattern) : d23 (change p 49 (some 71)) = d23 p := by
  change (if p 247 then d12 (change p 49 (some 71)) else d9 (change p 49 (some 71))) = d23 p
  rw [sub269, sub281]
  rfl
theorem sub283 (p : Pattern) : d24 (change p 49 (some 71)) = d24 p := by
  change (if p 246 then d23 (change p 49 (some 71)) else d9 (change p 49 (some 71))) = d24 p
  rw [sub282, sub281]
  rfl
theorem sub284 (p : Pattern) : d25 (change p 49 (some 71)) = d25 p := by
  change (if p 204 then d12 (change p 49 (some 71)) else d24 (change p 49 (some 71))) = d25 p
  rw [sub269, sub283]
  rfl
theorem sub285 (p : Pattern) : d26 (change p 49 (some 71)) = d26 p := by
  change (if p 182 then d25 (change p 49 (some 71)) else d24 (change p 49 (some 71))) = d26 p
  rw [sub284, sub283]
  rfl
theorem sub286 (p : Pattern) : d27 (change p 49 (some 71)) = d27 p := by
  change (if p 163 then d12 (change p 49 (some 71)) else d26 (change p 49 (some 71))) = d27 p
  rw [sub269, sub285]
  rfl
theorem sub287 (p : Pattern) : d28 (change p 49 (some 71)) = d28 p := by
  change (if p 162 then d27 (change p 49 (some 71)) else d21 (change p 49 (some 71))) = d28 p
  rw [sub286, sub279]
  rfl
theorem sub288 (p : Pattern) : d29 (change p 49 (some 71)) = d29 p := by
  change (if p 161 then d28 (change p 49 (some 71)) else d22 (change p 49 (some 71))) = d29 p
  rw [sub287, sub280]
  rfl
theorem sub289 (p : Pattern) : d2 (change p 49 (some 71)) = d2 p := by
  rfl
theorem sub290 (p : Pattern) : d30 (change p 49 (some 71)) = d30 p := by
  change (if p 247 then d12 (change p 49 (some 71)) else d2 (change p 49 (some 71))) = d30 p
  rw [sub269, sub289]
  rfl
theorem sub291 (p : Pattern) : d31 (change p 49 (some 71)) = d31 p := by
  change (if p 246 then d30 (change p 49 (some 71)) else d2 (change p 49 (some 71))) = d31 p
  rw [sub290, sub289]
  rfl
theorem sub292 (p : Pattern) : d32 (change p 49 (some 71)) = d32 p := by
  change (if p 204 then d12 (change p 49 (some 71)) else d31 (change p 49 (some 71))) = d32 p
  rw [sub269, sub291]
  rfl
theorem sub293 (p : Pattern) : d33 (change p 49 (some 71)) = d33 p := by
  change (if p 182 then d32 (change p 49 (some 71)) else d14 (change p 49 (some 71))) = d33 p
  rw [sub292, sub271]
  rfl
theorem sub294 (p : Pattern) : d6 (change p 49 (some 71)) = d6 p := by
  rfl
theorem sub295 (p : Pattern) : d34 (change p 49 (some 71)) = d34 p := by
  change (if p 247 then d12 (change p 49 (some 71)) else d6 (change p 49 (some 71))) = d34 p
  rw [sub269, sub294]
  rfl
theorem sub296 (p : Pattern) : d35 (change p 49 (some 71)) = d35 p := by
  change (if p 246 then d34 (change p 49 (some 71)) else d6 (change p 49 (some 71))) = d35 p
  rw [sub295, sub294]
  rfl
theorem sub297 (p : Pattern) : d36 (change p 49 (some 71)) = d36 p := by
  change (if p 204 then d12 (change p 49 (some 71)) else d35 (change p 49 (some 71))) = d36 p
  rw [sub269, sub296]
  rfl
theorem sub298 (p : Pattern) : d37 (change p 49 (some 71)) = d37 p := by
  change (if p 182 then d36 (change p 49 (some 71)) else d14 (change p 49 (some 71))) = d37 p
  rw [sub297, sub271]
  rfl
theorem sub299 (p : Pattern) : d38 (change p 49 (some 71)) = d38 p := by
  change (if p 163 then d37 (change p 49 (some 71)) else d33 (change p 49 (some 71))) = d38 p
  rw [sub298, sub293]
  rfl
theorem sub300 (p : Pattern) : d11 (change p 49 (some 71)) = d11 p := by
  rfl
theorem sub301 (p : Pattern) : d39 (change p 49 (some 71)) = d39 p := by
  change (if p 247 then d12 (change p 49 (some 71)) else d11 (change p 49 (some 71))) = d39 p
  rw [sub269, sub300]
  rfl
theorem sub302 (p : Pattern) : d40 (change p 49 (some 71)) = d40 p := by
  change (if p 246 then d39 (change p 49 (some 71)) else d11 (change p 49 (some 71))) = d40 p
  rw [sub301, sub300]
  rfl
theorem sub303 (p : Pattern) : d41 (change p 49 (some 71)) = d41 p := by
  change (if p 204 then d12 (change p 49 (some 71)) else d40 (change p 49 (some 71))) = d41 p
  rw [sub269, sub302]
  rfl
theorem sub304 (p : Pattern) : d42 (change p 49 (some 71)) = d42 p := by
  change (if p 182 then d41 (change p 49 (some 71)) else d14 (change p 49 (some 71))) = d42 p
  rw [sub303, sub271]
  rfl
theorem sub305 (p : Pattern) : d43 (change p 49 (some 71)) = d43 p := by
  change (if p 182 then d12 (change p 49 (some 71)) else d18 (change p 49 (some 71))) = d43 p
  rw [sub269, sub276]
  rfl
theorem sub306 (p : Pattern) : d44 (change p 49 (some 71)) = d44 p := by
  change (if p 163 then d43 (change p 49 (some 71)) else d42 (change p 49 (some 71))) = d44 p
  rw [sub305, sub304]
  rfl
theorem sub307 (p : Pattern) : d45 (change p 49 (some 71)) = d45 p := by
  change (if p 162 then d44 (change p 49 (some 71)) else d38 (change p 49 (some 71))) = d45 p
  rw [sub306, sub299]
  rfl
theorem sub308 (p : Pattern) : d46 (change p 49 (some 71)) = d46 p := by
  change (if p 182 then d12 (change p 49 (some 71)) else d14 (change p 49 (some 71))) = d46 p
  rw [sub269, sub271]
  rfl
theorem sub309 (p : Pattern) : d47 (change p 49 (some 71)) = d47 p := by
  change (if p 163 then d43 (change p 49 (some 71)) else d46 (change p 49 (some 71))) = d47 p
  rw [sub305, sub308]
  rfl
theorem sub310 (p : Pattern) : d48 (change p 49 (some 71)) = d48 p := by
  change (if p 182 then d12 (change p 49 (some 71)) else d24 (change p 49 (some 71))) = d48 p
  rw [sub269, sub283]
  rfl
theorem sub311 (p : Pattern) : d49 (change p 49 (some 71)) = d49 p := by
  change (if p 163 then d12 (change p 49 (some 71)) else d48 (change p 49 (some 71))) = d49 p
  rw [sub269, sub310]
  rfl
theorem sub312 (p : Pattern) : d50 (change p 49 (some 71)) = d50 p := by
  change (if p 162 then d49 (change p 49 (some 71)) else d47 (change p 49 (some 71))) = d50 p
  rw [sub311, sub309]
  rfl
theorem sub313 (p : Pattern) : d51 (change p 49 (some 71)) = d51 p := by
  change (if p 161 then d50 (change p 49 (some 71)) else d45 (change p 49 (some 71))) = d51 p
  rw [sub312, sub307]
  rfl
theorem sub314 (p : Pattern) : d52 (change p 49 (some 71)) = d52 p := by
  change (if p 160 then d51 (change p 49 (some 71)) else d29 (change p 49 (some 71))) = d52 p
  rw [sub313, sub288]
  rfl
theorem sub315 (p : Pattern) : d53 (change p 49 (some 71)) = d53 p := by
  change (if p 182 then d32 (change p 49 (some 71)) else d31 (change p 49 (some 71))) = d53 p
  rw [sub292, sub291]
  rfl
theorem sub316 (p : Pattern) : d54 (change p 49 (some 71)) = d54 p := by
  change (if p 163 then d53 (change p 49 (some 71)) else d16 (change p 49 (some 71))) = d54 p
  rw [sub315, sub273]
  rfl
theorem sub317 (p : Pattern) : d55 (change p 49 (some 71)) = d55 p := by
  change (if p 163 then d26 (change p 49 (some 71)) else d20 (change p 49 (some 71))) = d55 p
  rw [sub285, sub278]
  rfl
theorem sub318 (p : Pattern) : d56 (change p 49 (some 71)) = d56 p := by
  change (if p 162 then d55 (change p 49 (some 71)) else d54 (change p 49 (some 71))) = d56 p
  rw [sub317, sub316]
  rfl
theorem sub319 (p : Pattern) : d10 (change p 49 (some 71)) = d10 p := by
  rfl
theorem sub320 (p : Pattern) : d57 (change p 49 (some 71)) = d57 p := by
  change (if p 247 then d12 (change p 49 (some 71)) else d10 (change p 49 (some 71))) = d57 p
  rw [sub269, sub319]
  rfl
theorem sub321 (p : Pattern) : d58 (change p 49 (some 71)) = d58 p := by
  change (if p 246 then d57 (change p 49 (some 71)) else d10 (change p 49 (some 71))) = d58 p
  rw [sub320, sub319]
  rfl
theorem sub322 (p : Pattern) : d59 (change p 49 (some 71)) = d59 p := by
  change (if p 204 then d12 (change p 49 (some 71)) else d58 (change p 49 (some 71))) = d59 p
  rw [sub269, sub321]
  rfl
theorem sub323 (p : Pattern) : d60 (change p 49 (some 71)) = d60 p := by
  change (if p 182 then d59 (change p 49 (some 71)) else d58 (change p 49 (some 71))) = d60 p
  rw [sub322, sub321]
  rfl
theorem sub324 (p : Pattern) : d61 (change p 49 (some 71)) = d61 p := by
  change (if p 163 then d60 (change p 49 (some 71)) else d20 (change p 49 (some 71))) = d61 p
  rw [sub323, sub278]
  rfl
theorem sub325 (p : Pattern) : d62 (change p 49 (some 71)) = d62 p := by
  change (if p 182 then d41 (change p 49 (some 71)) else d40 (change p 49 (some 71))) = d62 p
  rw [sub303, sub302]
  rfl
theorem sub326 (p : Pattern) : d63 (change p 49 (some 71)) = d63 p := by
  change (if p 163 then d12 (change p 49 (some 71)) else d62 (change p 49 (some 71))) = d63 p
  rw [sub269, sub325]
  rfl
theorem sub327 (p : Pattern) : d64 (change p 49 (some 71)) = d64 p := by
  change (if p 162 then d63 (change p 49 (some 71)) else d61 (change p 49 (some 71))) = d64 p
  rw [sub326, sub324]
  rfl
theorem sub328 (p : Pattern) : d65 (change p 49 (some 71)) = d65 p := by
  change (if p 161 then d64 (change p 49 (some 71)) else d56 (change p 49 (some 71))) = d65 p
  rw [sub327, sub318]
  rfl
theorem sub329 (p : Pattern) : d66 (change p 49 (some 71)) = d66 p := by
  change (if p 182 then d12 (change p 49 (some 71)) else d31 (change p 49 (some 71))) = d66 p
  rw [sub269, sub291]
  rfl
theorem sub330 (p : Pattern) : d67 (change p 49 (some 71)) = d67 p := by
  change (if p 163 then d66 (change p 49 (some 71)) else d37 (change p 49 (some 71))) = d67 p
  rw [sub329, sub298]
  rfl
theorem sub331 (p : Pattern) : d68 (change p 49 (some 71)) = d68 p := by
  change (if p 163 then d48 (change p 49 (some 71)) else d43 (change p 49 (some 71))) = d68 p
  rw [sub310, sub305]
  rfl
theorem sub332 (p : Pattern) : d69 (change p 49 (some 71)) = d69 p := by
  change (if p 162 then d68 (change p 49 (some 71)) else d67 (change p 49 (some 71))) = d69 p
  rw [sub331, sub330]
  rfl
theorem sub333 (p : Pattern) : d70 (change p 49 (some 71)) = d70 p := by
  change (if p 182 then d12 (change p 49 (some 71)) else d58 (change p 49 (some 71))) = d70 p
  rw [sub269, sub321]
  rfl
theorem sub334 (p : Pattern) : d71 (change p 49 (some 71)) = d71 p := by
  change (if p 163 then d70 (change p 49 (some 71)) else d43 (change p 49 (some 71))) = d71 p
  rw [sub333, sub305]
  rfl
theorem sub335 (p : Pattern) : d72 (change p 49 (some 71)) = d72 p := by
  change (if p 182 then d12 (change p 49 (some 71)) else d40 (change p 49 (some 71))) = d72 p
  rw [sub269, sub302]
  rfl
theorem sub336 (p : Pattern) : d73 (change p 49 (some 71)) = d73 p := by
  change (if p 163 then d12 (change p 49 (some 71)) else d72 (change p 49 (some 71))) = d73 p
  rw [sub269, sub335]
  rfl
theorem sub337 (p : Pattern) : d74 (change p 49 (some 71)) = d74 p := by
  change (if p 162 then d73 (change p 49 (some 71)) else d71 (change p 49 (some 71))) = d74 p
  rw [sub336, sub334]
  rfl
theorem sub338 (p : Pattern) : d75 (change p 49 (some 71)) = d75 p := by
  change (if p 161 then d74 (change p 49 (some 71)) else d69 (change p 49 (some 71))) = d75 p
  rw [sub337, sub332]
  rfl
theorem sub339 (p : Pattern) : d76 (change p 49 (some 71)) = d76 p := by
  change (if p 160 then d75 (change p 49 (some 71)) else d65 (change p 49 (some 71))) = d76 p
  rw [sub338, sub328]
  rfl
theorem sub340 (p : Pattern) : d77 (change p 49 (some 71)) = d77 p := by
  change (if p 141 then d76 (change p 49 (some 71)) else d52 (change p 49 (some 71))) = d77 p
  rw [sub339, sub314]
  rfl
theorem sub341 (p : Pattern) : d78 (change p 49 (some 71)) = d78 p := by
  change (if p 182 then d36 (change p 49 (some 71)) else d35 (change p 49 (some 71))) = d78 p
  rw [sub297, sub296]
  rfl
theorem sub342 (p : Pattern) : d79 (change p 49 (some 71)) = d79 p := by
  change (if p 163 then d78 (change p 49 (some 71)) else d53 (change p 49 (some 71))) = d79 p
  rw [sub341, sub315]
  rfl
theorem sub343 (p : Pattern) : d80 (change p 49 (some 71)) = d80 p := by
  change (if p 162 then d63 (change p 49 (some 71)) else d79 (change p 49 (some 71))) = d80 p
  rw [sub326, sub342]
  rfl
theorem sub344 (p : Pattern) : d81 (change p 49 (some 71)) = d81 p := by
  change (if p 161 then d12 (change p 49 (some 71)) else d80 (change p 49 (some 71))) = d81 p
  rw [sub269, sub343]
  rfl
theorem sub345 (p : Pattern) : d82 (change p 49 (some 71)) = d82 p := by
  change (if p 160 then d81 (change p 49 (some 71)) else d29 (change p 49 (some 71))) = d82 p
  rw [sub344, sub288]
  rfl
theorem sub346 (p : Pattern) : d83 (change p 49 (some 71)) = d83 p := by
  change (if p 163 then d12 (change p 49 (some 71)) else d78 (change p 49 (some 71))) = d83 p
  rw [sub269, sub341]
  rfl
theorem sub347 (p : Pattern) : d84 (change p 49 (some 71)) = d84 p := by
  change (if p 162 then d12 (change p 49 (some 71)) else d83 (change p 49 (some 71))) = d84 p
  rw [sub269, sub346]
  rfl
theorem sub348 (p : Pattern) : d85 (change p 49 (some 71)) = d85 p := by
  change (if p 161 then d12 (change p 49 (some 71)) else d84 (change p 49 (some 71))) = d85 p
  rw [sub269, sub347]
  rfl
theorem sub349 (p : Pattern) : d86 (change p 49 (some 71)) = d86 p := by
  change (if p 160 then d85 (change p 49 (some 71)) else d65 (change p 49 (some 71))) = d86 p
  rw [sub348, sub328]
  rfl
theorem sub350 (p : Pattern) : d87 (change p 49 (some 71)) = d87 p := by
  change (if p 141 then d86 (change p 49 (some 71)) else d82 (change p 49 (some 71))) = d87 p
  rw [sub349, sub345]
  rfl
theorem sub351 (p : Pattern) : d88 (change p 49 (some 71)) = d88 p := by
  change (if p 138 then d87 (change p 49 (some 71)) else d77 (change p 49 (some 71))) = d88 p
  rw [sub350, sub340]
  rfl
theorem sub352 (p : Pattern) : d89 (change p 49 (some 71)) = d89 p := by
  change (if p 163 then d62 (change p 49 (some 71)) else d26 (change p 49 (some 71))) = d89 p
  rw [sub325, sub285]
  rfl
theorem sub353 (p : Pattern) : d90 (change p 49 (some 71)) = d90 p := by
  change (if p 162 then d63 (change p 49 (some 71)) else d89 (change p 49 (some 71))) = d90 p
  rw [sub326, sub352]
  rfl
theorem sub354 (p : Pattern) : d91 (change p 49 (some 71)) = d91 p := by
  change (if p 162 then d12 (change p 49 (some 71)) else d63 (change p 49 (some 71))) = d91 p
  rw [sub269, sub326]
  rfl
theorem sub355 (p : Pattern) : d92 (change p 49 (some 71)) = d92 p := by
  change (if p 161 then d91 (change p 49 (some 71)) else d90 (change p 49 (some 71))) = d92 p
  rw [sub354, sub353]
  rfl
theorem sub356 (p : Pattern) : d93 (change p 49 (some 71)) = d93 p := by
  change (if p 161 then d12 (change p 49 (some 71)) else d91 (change p 49 (some 71))) = d93 p
  rw [sub269, sub354]
  rfl
theorem sub357 (p : Pattern) : d94 (change p 49 (some 71)) = d94 p := by
  change (if p 160 then d93 (change p 49 (some 71)) else d92 (change p 49 (some 71))) = d94 p
  rw [sub356, sub355]
  rfl
theorem sub358 (p : Pattern) : d95 (change p 49 (some 71)) = d95 p := by
  change (if p 160 then d12 (change p 49 (some 71)) else d93 (change p 49 (some 71))) = d95 p
  rw [sub269, sub356]
  rfl
theorem sub359 (p : Pattern) : d96 (change p 49 (some 71)) = d96 p := by
  change (if p 141 then d95 (change p 49 (some 71)) else d94 (change p 49 (some 71))) = d96 p
  rw [sub358, sub357]
  rfl
end NetHack.Sokoban22Refined85
