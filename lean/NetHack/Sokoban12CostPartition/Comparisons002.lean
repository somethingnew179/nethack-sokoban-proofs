/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare280 (p : Pattern) (guard : d771 p = 1) : d136 p ≤ (0 : Int) + d133 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d771, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare276 p hg
    simpa only [d771, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d753 p = 1 := by simpa only [d771, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare279 p hg
    simpa only [d771, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare281 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d151 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare282 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (0 : Int) + d7 p := by
  omega
theorem compare283 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare284 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d4 p := by
  change (2 : Int) ≤ (0 : Int) + 4
  decide
theorem compare285 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (0 : Int) + d54 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare283 p hg
    simpa only [d6, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare284 p hg
    simpa only [d6, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare286 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (0 : Int) + d55 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare283 p hg
    simpa only [d7, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare285 p hg
    simpa only [d7, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare287 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (0 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare288 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (0 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare287 p hg
    simpa only [d56, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d56, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare289 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (0 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d57, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare288 p hg
    simpa only [d57, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare290 (p : Pattern) (guard : d1 p = 1) : d139 p ≤ (0 : Int) + d139 p := by
  omega
theorem compare291 (p : Pattern) (guard : d1 p = 1) : d153 p ≤ (0 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d153, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare289 p hg
    simpa only [d153, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d153, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare290 p hg
    simpa only [d153, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare292 (p : Pattern) (guard : d1 p = 1) : d141 p ≤ (0 : Int) + d141 p := by
  omega
theorem compare293 (p : Pattern) (guard : d1 p = 1) : d154 p ≤ (0 : Int) + d142 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d154, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare291 p hg
    simpa only [d154, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d154, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare292 p hg
    simpa only [d154, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare294 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare295 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (0 : Int) + d11 p := by
  omega
theorem compare296 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d3 p := by
  change (1 : Int) ≤ (0 : Int) + 3
  decide
theorem compare297 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (0 : Int) + d9 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare283 p hg
    simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare296 p hg
    simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare298 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d5 p := by
  change (3 : Int) ≤ (0 : Int) + 5
  decide
theorem compare299 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (0 : Int) + d58 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare284 p hg
    simpa only [d9, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare298 p hg
    simpa only [d9, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare300 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (0 : Int) + d59 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare297 p hg
    simpa only [d10, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare299 p hg
    simpa only [d10, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare301 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (0 : Int) + d60 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d11, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare297 p hg
    simpa only [d11, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d11, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare300 p hg
    simpa only [d11, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare302 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (0 : Int) + d125 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare301 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare303 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (0 : Int) + d60 p := by
  omega
theorem compare304 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (0 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare302 p hg
    simpa only [d61, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare303 p hg
    simpa only [d61, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare305 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (0 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare288 p hg
    simpa only [d62, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare304 p hg
    simpa only [d62, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare306 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (0 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare294 p hg
    simpa only [d63, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare305 p hg
    simpa only [d63, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare307 (p : Pattern) (guard : d1 p = 1) : d146 p ≤ (0 : Int) + d146 p := by
  omega
theorem compare308 (p : Pattern) (guard : d1 p = 1) : d155 p ≤ (0 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d155, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare306 p hg
    simpa only [d155, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d155, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare307 p hg
    simpa only [d155, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare309 (p : Pattern) (guard : d1 p = 1) : d148 p ≤ (0 : Int) + d148 p := by
  omega
theorem compare310 (p : Pattern) (guard : d1 p = 1) : d156 p ≤ (0 : Int) + d149 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d156, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare308 p hg
    simpa only [d156, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d156, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare309 p hg
    simpa only [d156, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare311 (p : Pattern) (guard : d1 p = 1) : d157 p ≤ (0 : Int) + d150 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d157, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare293 p hg
    simpa only [d157, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d157, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare310 p hg
    simpa only [d157, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare312 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare313 (p : Pattern) (guard : d1 p = 1) : d158 p ≤ (0 : Int) + d151 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d158, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare311 p hg
    simpa only [d158, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d158, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare312 p hg
    simpa only [d158, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare314 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d151 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare315 (p : Pattern) (guard : d753 p = 1) : d159 p ≤ (0 : Int) + d151 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d753, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare313 p hg
    simpa only [d753, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d753, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare314 p hg
    simpa only [d753, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare316 (p : Pattern) (guard : d771 p = 1) : d160 p ≤ (0 : Int) + d151 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d771, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare281 p hg
    simpa only [d771, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d753 p = 1 := by simpa only [d771, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare315 p hg
    simpa only [d771, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare317 (p : Pattern) (guard : d771 p = 1) : d161 p ≤ (0 : Int) + d772 p := by
  cases selected : p 108 with
  | false =>
    have hg : d771 p = 1 := by simpa only [d161, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare280 p hg
    simpa only [d161, d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d771 p = 1 := by simpa only [d161, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare316 p hg
    simpa only [d161, d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare318 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare319 (p : Pattern) (guard : d742 p = 1) : d57 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare318 p hg
    simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare320 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (0 : Int) + d63 p := by
  omega
theorem compare321 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare322 (p : Pattern) (guard : d742 p = 1) : d63 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare321 p hg
    simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare323 (p : Pattern) (guard : d742 p = 1) : d64 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d64, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare319 p hg
    simpa only [d64, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d64, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare322 p hg
    simpa only [d64, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare324 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (0 : Int) + d106 p := by
  omega
theorem compare325 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare326 (p : Pattern) (guard : d742 p = 1) : d108 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d108, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare324 p hg
    simpa only [d742, d108, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d108, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare325 p hg
    simpa only [d742, d108, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare327 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (0 : Int) + d109 p := by
  omega
theorem compare328 (p : Pattern) (guard : d0 p = 1) : d110 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare329 (p : Pattern) (guard : d742 p = 1) : d111 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d111, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare327 p hg
    simpa only [d742, d111, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d111, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare328 p hg
    simpa only [d742, d111, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare330 (p : Pattern) (guard : d742 p = 1) : d112 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d112, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare326 p hg
    simpa only [d112, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d112, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare329 p hg
    simpa only [d112, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare331 (p : Pattern) (guard : d742 p = 1) : d113 p ≤ (0 : Int) + d232 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d113, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare323 p hg
    simpa only [d113, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d113, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare330 p hg
    simpa only [d113, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare332 (p : Pattern) (guard : d0 p = 1) : d114 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare333 (p : Pattern) (guard : d742 p = 1) : d115 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d115, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d742, d115, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d115, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare332 p hg
    simpa only [d742, d115, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare334 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare335 (p : Pattern) (guard : d742 p = 1) : d117 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d117, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d742, d117, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d117, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare334 p hg
    simpa only [d742, d117, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare336 (p : Pattern) (guard : d742 p = 1) : d118 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d118, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare333 p hg
    simpa only [d118, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d118, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare335 p hg
    simpa only [d118, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare337 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (0 : Int) + d122 p := by
  omega
theorem compare338 (p : Pattern) (guard : d0 p = 1) : d123 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare339 (p : Pattern) (guard : d742 p = 1) : d124 p ≤ (0 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d124, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare337 p hg
    simpa only [d742, d124, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d124, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare338 p hg
    simpa only [d742, d124, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare340 (p : Pattern) (guard : d1 p = 1) : d129 p ≤ (0 : Int) + d129 p := by
  omega
theorem compare341 (p : Pattern) (guard : d0 p = 1) : d130 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare342 (p : Pattern) (guard : d742 p = 1) : d131 p ≤ (0 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d131, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare340 p hg
    simpa only [d742, d131, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d131, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare341 p hg
    simpa only [d742, d131, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare343 (p : Pattern) (guard : d742 p = 1) : d132 p ≤ (0 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d132, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare339 p hg
    simpa only [d132, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d132, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare342 p hg
    simpa only [d132, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare344 (p : Pattern) (guard : d742 p = 1) : d133 p ≤ (0 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d133, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare336 p hg
    simpa only [d133, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d133, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare343 p hg
    simpa only [d133, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare345 (p : Pattern) (guard : d742 p = 1) : d134 p ≤ (0 : Int) + d315 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d134, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare331 p hg
    simpa only [d134, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d134, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare344 p hg
    simpa only [d134, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare346 (p : Pattern) (guard : d742 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare347 (p : Pattern) (guard : d742 p = 1) : d135 p ≤ (0 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d135, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare344 p hg
    simpa only [d135, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d135, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d135, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare348 (p : Pattern) (guard : d742 p = 1) : d136 p ≤ (0 : Int) + d316 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d136, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare345 p hg
    simpa only [d136, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d136, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare347 p hg
    simpa only [d136, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare349 (p : Pattern) (guard : d742 p = 1) : d67 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d67, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare323 p hg
    simpa only [d67, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d67, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d67, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare350 (p : Pattern) (guard : d1 p = 1) : d140 p ≤ (0 : Int) + d140 p := by
  omega
theorem compare351 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare352 (p : Pattern) (guard : d742 p = 1) : d142 p ≤ (0 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d142, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare350 p hg
    simpa only [d742, d142, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d142, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare351 p hg
    simpa only [d742, d142, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare353 (p : Pattern) (guard : d1 p = 1) : d147 p ≤ (0 : Int) + d147 p := by
  omega
theorem compare354 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare355 (p : Pattern) (guard : d742 p = 1) : d149 p ≤ (0 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d149, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare353 p hg
    simpa only [d742, d149, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d149, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare354 p hg
    simpa only [d742, d149, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare356 (p : Pattern) (guard : d742 p = 1) : d150 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d150, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare352 p hg
    simpa only [d150, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d150, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare355 p hg
    simpa only [d150, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare357 (p : Pattern) (guard : d742 p = 1) : d151 p ≤ (0 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d151, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare356 p hg
    simpa only [d151, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d151, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d151, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare358 (p : Pattern) (guard : d742 p = 1) : d152 p ≤ (0 : Int) + d317 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d152, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare349 p hg
    simpa only [d152, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d152, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare357 p hg
    simpa only [d152, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare359 (p : Pattern) (guard : d1 p = 1) : d153 p ≤ (0 : Int) + d153 p := by
  omega
theorem compare360 (p : Pattern) (guard : d742 p = 1) : d154 p ≤ (0 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d154, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare359 p hg
    simpa only [d742, d154, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d154, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare351 p hg
    simpa only [d742, d154, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare361 (p : Pattern) (guard : d1 p = 1) : d155 p ≤ (0 : Int) + d155 p := by
  omega
theorem compare362 (p : Pattern) (guard : d742 p = 1) : d156 p ≤ (0 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d156, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare361 p hg
    simpa only [d742, d156, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d156, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare354 p hg
    simpa only [d742, d156, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare363 (p : Pattern) (guard : d742 p = 1) : d157 p ≤ (0 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d157, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare360 p hg
    simpa only [d157, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d157, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare362 p hg
    simpa only [d157, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare364 (p : Pattern) (guard : d742 p = 1) : d158 p ≤ (0 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d158, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare363 p hg
    simpa only [d158, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d158, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d158, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare365 (p : Pattern) (guard : d742 p = 1) : d159 p ≤ (0 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d159, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare364 p hg
    simpa only [d159, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d159, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d159, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare366 (p : Pattern) (guard : d742 p = 1) : d160 p ≤ (0 : Int) + d318 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d160, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare358 p hg
    simpa only [d160, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d160, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare365 p hg
    simpa only [d160, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare367 (p : Pattern) (guard : d742 p = 1) : d161 p ≤ (0 : Int) + d319 p := by
  cases selected : p 108 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d161, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare348 p hg
    simpa only [d161, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d161, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare366 p hg
    simpa only [d161, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare368 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d135 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare369 (p : Pattern) (guard : d740 p = 1) : d199 p ≤ (0 : Int) + d136 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d740, d199, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42 p hg
    simpa only [d740, d199, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d740, d199, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare368 p hg
    simpa only [d740, d199, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare370 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d159 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare371 (p : Pattern) (guard : d740 p = 1) : d200 p ≤ (0 : Int) + d160 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d740, d200, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d740, d200, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d740, d200, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare370 p hg
    simpa only [d740, d200, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare372 (p : Pattern) (guard : d740 p = 1) : d201 p ≤ (0 : Int) + d161 p := by
  cases selected : p 108 with
  | false =>
    have hg : d740 p = 1 := by simpa only [d201, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare369 p hg
    simpa only [d201, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d740 p = 1 := by simpa only [d201, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare371 p hg
    simpa only [d201, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare373 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d244 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare374 (p : Pattern) (guard : d773 p = 1) : d199 p ≤ (0 : Int) + d316 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d773, d199, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare345 p hg
    simpa only [d773, d199, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, d199, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare373 p hg
    simpa only [d773, d199, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare375 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d256 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare376 (p : Pattern) (guard : d773 p = 1) : d200 p ≤ (0 : Int) + d318 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d773, d200, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare358 p hg
    simpa only [d773, d200, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, d200, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare375 p hg
    simpa only [d773, d200, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare377 (p : Pattern) (guard : d773 p = 1) : d201 p ≤ (0 : Int) + d319 p := by
  cases selected : p 108 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d201, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare374 p hg
    simpa only [d201, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d773 p = 1 := by simpa only [d201, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare376 p hg
    simpa only [d201, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare378 (p : Pattern) (guard : d741 p = 1) : d64 p ≤ (2 : Int) + d64 p := by
  omega
theorem compare379 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (2 : Int) + d106 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare380 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare381 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare380 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare382 (p : Pattern) (guard : d741 p = 1) : d108 p ≤ (2 : Int) + d106 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare379 p hg
    simpa only [d741, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare381 p hg
    simpa only [d741, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare383 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (2 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare384 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare89 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare385 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (2 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare384 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare386 (p : Pattern) (guard : d741 p = 1) : d111 p ≤ (2 : Int) + d109 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare383 p hg
    simpa only [d741, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare385 p hg
    simpa only [d741, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare387 (p : Pattern) (guard : d741 p = 1) : d112 p ≤ (2 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare382 p hg
    simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare386 p hg
    simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare388 (p : Pattern) (guard : d741 p = 1) : d113 p ≤ (2 : Int) + d228 p := by
  cases selected : p 134 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d113, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare378 p hg
    simpa only [d113, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d113, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare387 p hg
    simpa only [d113, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare389 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (2 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare390 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (2 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare50 p hg
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare79 p hg
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare391 (p : Pattern) (guard : d741 p = 1) : d115 p ≤ (2 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare389 p hg
    simpa only [d741, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare390 p hg
    simpa only [d741, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare392 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (2 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare393 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare92 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare394 (p : Pattern) (guard : d741 p = 1) : d117 p ≤ (2 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare392 p hg
    simpa only [d741, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare393 p hg
    simpa only [d741, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare395 (p : Pattern) (guard : d741 p = 1) : d118 p ≤ (2 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d118, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare391 p hg
    simpa only [d118, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d118, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare394 p hg
    simpa only [d118, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare396 (p : Pattern) (guard : d0 p = 1) : d122 p ≤ (2 : Int) + d122 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare397 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (2 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare117 p hg
    simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9 p hg
    simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare398 (p : Pattern) (guard : d1 p = 1) : d123 p ≤ (2 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d123, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare397 p hg
    simpa only [d123, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d123, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare99 p hg
    simpa only [d123, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare399 (p : Pattern) (guard : d741 p = 1) : d124 p ≤ (2 : Int) + d122 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare396 p hg
    simpa only [d741, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare398 p hg
    simpa only [d741, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare400 (p : Pattern) (guard : d0 p = 1) : d129 p ≤ (2 : Int) + d129 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare401 (p : Pattern) (guard : d1 p = 1) : d128 p ≤ (2 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare126 p hg
    simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare402 (p : Pattern) (guard : d1 p = 1) : d130 p ≤ (2 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d130, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare401 p hg
    simpa only [d130, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d130, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare106 p hg
    simpa only [d130, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare403 (p : Pattern) (guard : d741 p = 1) : d131 p ≤ (2 : Int) + d129 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare400 p hg
    simpa only [d741, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare402 p hg
    simpa only [d741, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare404 (p : Pattern) (guard : d741 p = 1) : d132 p ≤ (2 : Int) + d775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d132, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare399 p hg
    simpa only [d132, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d132, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare403 p hg
    simpa only [d132, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare405 (p : Pattern) (guard : d741 p = 1) : d133 p ≤ (2 : Int) + d776 p := by
  cases selected : p 134 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d133, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare395 p hg
    simpa only [d133, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d133, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare404 p hg
    simpa only [d133, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare406 (p : Pattern) (guard : d741 p = 1) : d134 p ≤ (2 : Int) + d777 p := by
  cases selected : p 133 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d134, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare388 p hg
    simpa only [d134, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d134, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare405 p hg
    simpa only [d134, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare407 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (2 : Int) + d778 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare408 (p : Pattern) (guard : d774 p = 1) : d199 p ≤ (2 : Int) + d779 p := by
  cases selected : p 132 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d774, d199, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare406 p hg
    simpa only [d774, d199, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d199, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare407 p hg
    simpa only [d774, d199, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare409 (p : Pattern) (guard : d741 p = 1) : d67 p ≤ (2 : Int) + d67 p := by
  omega
theorem compare410 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (2 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare411 (p : Pattern) (guard : d1 p = 1) : d137 p ≤ (2 : Int) + d137 p := by
  omega
theorem compare412 (p : Pattern) (guard : d1 p = 1) : d139 p ≤ (2 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d139, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare117 p hg
    simpa only [d139, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d139, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare411 p hg
    simpa only [d139, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare413 (p : Pattern) (guard : d1 p = 1) : d141 p ≤ (2 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d141, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare412 p hg
    simpa only [d141, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d141, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare137 p hg
    simpa only [d141, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare414 (p : Pattern) (guard : d741 p = 1) : d142 p ≤ (2 : Int) + d140 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare410 p hg
    simpa only [d741, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare413 p hg
    simpa only [d741, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare415 (p : Pattern) (guard : d0 p = 1) : d147 p ≤ (2 : Int) + d147 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare416 (p : Pattern) (guard : d1 p = 1) : d144 p ≤ (2 : Int) + d144 p := by
  omega
theorem compare417 (p : Pattern) (guard : d1 p = 1) : d146 p ≤ (2 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d146, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare126 p hg
    simpa only [d146, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d146, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare416 p hg
    simpa only [d146, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare418 (p : Pattern) (guard : d1 p = 1) : d148 p ≤ (2 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d148, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare417 p hg
    simpa only [d148, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d148, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare143 p hg
    simpa only [d148, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare419 (p : Pattern) (guard : d741 p = 1) : d149 p ≤ (2 : Int) + d147 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare415 p hg
    simpa only [d741, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d741, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
