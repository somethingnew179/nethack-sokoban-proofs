/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons192
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare27020 (p : Pattern) (guard : d5268 p = 1) : d3257 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3257, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15733 p hg
    simpa only [d5268, d3257, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3257, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27019 p hg
    simpa only [d5268, d3257, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27021 (p : Pattern) (guard : d5269 p = 1) : d3257 p ≤ (2 : Int) + d40 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27018 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27020 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27022 (p : Pattern) (guard : d5269 p = 1) : d3258 p ≤ (2 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3258, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27021 p hg
    simpa only [d3258, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3258, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3258, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27023 (p : Pattern) (guard : d5269 p = 1) : d3259 p ≤ (2 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3259, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26977 p hg
    simpa only [d3259, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3259, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27022 p hg
    simpa only [d3259, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27024 (p : Pattern) (guard : d5269 p = 1) : d3260 p ≤ (2 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3260, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26991 p hg
    simpa only [d3260, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3260, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3260, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27025 (p : Pattern) (guard : d5269 p = 1) : d3261 p ≤ (2 : Int) + d44 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3261, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27023 p hg
    simpa only [d3261, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3261, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27024 p hg
    simpa only [d3261, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27026 (p : Pattern) (guard : d5269 p = 1) : d3262 p ≤ (2 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3262, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27017 p hg
    simpa only [d3262, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3262, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27025 p hg
    simpa only [d3262, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27027 (p : Pattern) (guard : d5269 p = 1) : d3263 p ≤ (2 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3263, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26977 p hg
    simpa only [d3263, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3263, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3263, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27028 (p : Pattern) (guard : d5269 p = 1) : d3264 p ≤ (2 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3264, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27027 p hg
    simpa only [d3264, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3264, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27024 p hg
    simpa only [d3264, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27029 (p : Pattern) (guard : d5269 p = 1) : d3265 p ≤ (2 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3265, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26999 p hg
    simpa only [d3265, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3265, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3265, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27030 (p : Pattern) (guard : d5269 p = 1) : d3266 p ≤ (2 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3266, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27029 p hg
    simpa only [d3266, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3266, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3266, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27031 (p : Pattern) (guard : d5269 p = 1) : d3267 p ≤ (2 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3267, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27028 p hg
    simpa only [d3267, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3267, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27030 p hg
    simpa only [d3267, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27032 (p : Pattern) (guard : d5269 p = 1) : d3268 p ≤ (2 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3268, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27026 p hg
    simpa only [d3268, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3268, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27031 p hg
    simpa only [d3268, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27033 (p : Pattern) (guard : d5269 p = 1) : d3269 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3269, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27004 p hg
    simpa only [d3269, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3269, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27032 p hg
    simpa only [d3269, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27034 (p : Pattern) (guard : d0 p = 1) : d3271 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27035 (p : Pattern) (guard : d5269 p = 1) : d3272 p ≤ (2 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, d3272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27034 p hg
    simpa only [d5269, d3272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, d3272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26974 p hg
    simpa only [d5269, d3272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27036 (p : Pattern) (guard : d5269 p = 1) : d3273 p ≤ (2 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27035 p hg
    simpa only [d3273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26977 p hg
    simpa only [d3273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27037 (p : Pattern) (guard : d5269 p = 1) : d3274 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3274, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27036 p hg
    simpa only [d3274, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3274, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26980 p hg
    simpa only [d3274, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27038 (p : Pattern) (guard : d5269 p = 1) : d3275 p ≤ (2 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3275, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27008 p hg
    simpa only [d3275, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3275, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27009 p hg
    simpa only [d3275, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27039 (p : Pattern) (guard : d5269 p = 1) : d3276 p ≤ (2 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3276, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27037 p hg
    simpa only [d3276, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3276, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27038 p hg
    simpa only [d3276, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27040 (p : Pattern) (guard : d5269 p = 1) : d3277 p ≤ (2 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3277, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26993 p hg
    simpa only [d3277, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3277, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27001 p hg
    simpa only [d3277, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27041 (p : Pattern) (guard : d5269 p = 1) : d3278 p ≤ (2 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3278, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27039 p hg
    simpa only [d3278, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3278, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27040 p hg
    simpa only [d3278, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27042 (p : Pattern) (guard : d0 p = 1) : d3279 p ≤ (2 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27043 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27044 (p : Pattern) (guard : d5268 p = 1) : d3279 p ≤ (2 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3279, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15723 p hg
    simpa only [d5268, d3279, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3279, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27043 p hg
    simpa only [d5268, d3279, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27045 (p : Pattern) (guard : d5269 p = 1) : d3279 p ≤ (2 : Int) + d58 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27042 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27044 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27046 (p : Pattern) (guard : d5269 p = 1) : d3280 p ≤ (2 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3280, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27045 p hg
    simpa only [d3280, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3280, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3280, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27047 (p : Pattern) (guard : d5269 p = 1) : d3281 p ≤ (2 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3281, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27045 p hg
    simpa only [d3281, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3281, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27046 p hg
    simpa only [d3281, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27048 (p : Pattern) (guard : d5269 p = 1) : d3282 p ≤ (2 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3282, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26993 p hg
    simpa only [d3282, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3282, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27047 p hg
    simpa only [d3282, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27049 (p : Pattern) (guard : d5269 p = 1) : d3283 p ≤ (2 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3283, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27021 p hg
    simpa only [d3283, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3283, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27022 p hg
    simpa only [d3283, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27050 (p : Pattern) (guard : d5269 p = 1) : d3284 p ≤ (2 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3284, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27049 p hg
    simpa only [d3284, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3284, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3284, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27051 (p : Pattern) (guard : d5269 p = 1) : d3285 p ≤ (2 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3285, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27048 p hg
    simpa only [d3285, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3285, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27050 p hg
    simpa only [d3285, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27052 (p : Pattern) (guard : d5269 p = 1) : d3286 p ≤ (2 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3286, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27041 p hg
    simpa only [d3286, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3286, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27051 p hg
    simpa only [d3286, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27053 (p : Pattern) (guard : d5269 p = 1) : d3287 p ≤ (2 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3287, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27008 p hg
    simpa only [d3287, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3287, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3287, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27054 (p : Pattern) (guard : d5269 p = 1) : d3288 p ≤ (2 : Int) + d67 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3288, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27016 p hg
    simpa only [d3288, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3288, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27053 p hg
    simpa only [d3288, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27055 (p : Pattern) (guard : d5269 p = 1) : d3289 p ≤ (2 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3289, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27024 p hg
    simpa only [d3289, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3289, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27029 p hg
    simpa only [d3289, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27056 (p : Pattern) (guard : d5269 p = 1) : d3290 p ≤ (2 : Int) + d69 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3290, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27054 p hg
    simpa only [d3290, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3290, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27055 p hg
    simpa only [d3290, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27057 (p : Pattern) (guard : d5269 p = 1) : d3291 p ≤ (2 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3291, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27045 p hg
    simpa only [d3291, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3291, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3291, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27058 (p : Pattern) (guard : d5269 p = 1) : d3292 p ≤ (2 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3292, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27024 p hg
    simpa only [d3292, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3292, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27057 p hg
    simpa only [d3292, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27059 (p : Pattern) (guard : d5269 p = 1) : d3293 p ≤ (2 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3293, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27021 p hg
    simpa only [d3293, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3293, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3293, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27060 (p : Pattern) (guard : d5269 p = 1) : d3294 p ≤ (2 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3294, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27059 p hg
    simpa only [d3294, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3294, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3294, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27061 (p : Pattern) (guard : d5269 p = 1) : d3295 p ≤ (2 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3295, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27058 p hg
    simpa only [d3295, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3295, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27060 p hg
    simpa only [d3295, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27062 (p : Pattern) (guard : d5269 p = 1) : d3296 p ≤ (2 : Int) + d75 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3296, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27056 p hg
    simpa only [d3296, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3296, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27061 p hg
    simpa only [d3296, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27063 (p : Pattern) (guard : d5269 p = 1) : d3297 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3297, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27052 p hg
    simpa only [d3297, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3297, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27062 p hg
    simpa only [d3297, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27064 (p : Pattern) (guard : d5269 p = 1) : d3298 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3298, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27033 p hg
    simpa only [d3298, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3298, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27063 p hg
    simpa only [d3298, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27065 (p : Pattern) (guard : d5269 p = 1) : d3299 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3299, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26987 p hg
    simpa only [d3299, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3299, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26994 p hg
    simpa only [d3299, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27066 (p : Pattern) (guard : d5269 p = 1) : d3300 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3300, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27065 p hg
    simpa only [d3300, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3300, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27003 p hg
    simpa only [d3300, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27067 (p : Pattern) (guard : d5269 p = 1) : d3301 p ≤ (2 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3301, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27014 p hg
    simpa only [d3301, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3301, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27015 p hg
    simpa only [d3301, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27068 (p : Pattern) (guard : d5269 p = 1) : d3302 p ≤ (2 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3302, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27038 p hg
    simpa only [d3302, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3302, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27067 p hg
    simpa only [d3302, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27069 (p : Pattern) (guard : d5269 p = 1) : d3303 p ≤ (2 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3303, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27068 p hg
    simpa only [d3303, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3303, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27050 p hg
    simpa only [d3303, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27070 (p : Pattern) (guard : d5269 p = 1) : d3304 p ≤ (2 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3304, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27069 p hg
    simpa only [d3304, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3304, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3304, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27071 (p : Pattern) (guard : d5269 p = 1) : d3305 p ≤ (2 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3305, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27066 p hg
    simpa only [d3305, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3305, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27070 p hg
    simpa only [d3305, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27072 (p : Pattern) (guard : d5269 p = 1) : d3306 p ≤ (2 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3306, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26987 p hg
    simpa only [d3306, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3306, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27038 p hg
    simpa only [d3306, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27073 (p : Pattern) (guard : d5269 p = 1) : d3307 p ≤ (2 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3307, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27072 p hg
    simpa only [d3307, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3307, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27040 p hg
    simpa only [d3307, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27074 (p : Pattern) (guard : d5269 p = 1) : d3308 p ≤ (2 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3308, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27073 p hg
    simpa only [d3308, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3308, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27051 p hg
    simpa only [d3308, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27075 (p : Pattern) (guard : d5269 p = 1) : d3309 p ≤ (2 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3309, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27067 p hg
    simpa only [d3309, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3309, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3309, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27076 (p : Pattern) (guard : d5269 p = 1) : d3310 p ≤ (2 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3310, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27075 p hg
    simpa only [d3310, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3310, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3310, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27077 (p : Pattern) (guard : d5269 p = 1) : d3311 p ≤ (2 : Int) + d85 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3311, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27076 p hg
    simpa only [d3311, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3311, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3311, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27078 (p : Pattern) (guard : d5269 p = 1) : d3312 p ≤ (2 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3312, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27074 p hg
    simpa only [d3312, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3312, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27077 p hg
    simpa only [d3312, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27079 (p : Pattern) (guard : d5269 p = 1) : d3313 p ≤ (2 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3313, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27071 p hg
    simpa only [d3313, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3313, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27078 p hg
    simpa only [d3313, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27080 (p : Pattern) (guard : d5269 p = 1) : d3314 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3314, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27064 p hg
    simpa only [d3314, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3314, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27079 p hg
    simpa only [d3314, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27081 (p : Pattern) (guard : d5269 p = 1) : d3315 p ≤ (2 : Int) + d89 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3315, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27001 p hg
    simpa only [d3315, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3315, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27049 p hg
    simpa only [d3315, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27082 (p : Pattern) (guard : d5269 p = 1) : d3316 p ≤ (2 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3316, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27081 p hg
    simpa only [d3316, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3316, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27050 p hg
    simpa only [d3316, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27083 (p : Pattern) (guard : d5269 p = 1) : d3317 p ≤ (2 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3317, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27050 p hg
    simpa only [d3317, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3317, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3317, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27084 (p : Pattern) (guard : d5269 p = 1) : d3318 p ≤ (2 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3318, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27082 p hg
    simpa only [d3318, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3318, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27083 p hg
    simpa only [d3318, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27085 (p : Pattern) (guard : d5269 p = 1) : d3319 p ≤ (2 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3319, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27083 p hg
    simpa only [d3319, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3319, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3319, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27086 (p : Pattern) (guard : d5269 p = 1) : d3320 p ≤ (2 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3320, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27084 p hg
    simpa only [d3320, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3320, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27085 p hg
    simpa only [d3320, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27087 (p : Pattern) (guard : d5269 p = 1) : d3321 p ≤ (2 : Int) + d95 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3321, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27085 p hg
    simpa only [d3321, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3321, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3321, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27088 (p : Pattern) (guard : d5269 p = 1) : d3322 p ≤ (2 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3322, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27086 p hg
    simpa only [d3322, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3322, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27087 p hg
    simpa only [d3322, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27089 (p : Pattern) (guard : d5269 p = 1) : d3323 p ≤ (2 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3323, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27079 p hg
    simpa only [d3323, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3323, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27088 p hg
    simpa only [d3323, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27090 (p : Pattern) (guard : d5269 p = 1) : d3324 p ≤ (2 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3324, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27080 p hg
    simpa only [d3324, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3324, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27089 p hg
    simpa only [d3324, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27091 (p : Pattern) (guard : d5269 p = 1) : d3325 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26985 p hg
    simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26987 p hg
    simpa only [d3325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27092 (p : Pattern) (guard : d5269 p = 1) : d3326 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3326, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27091 p hg
    simpa only [d3326, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3326, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26994 p hg
    simpa only [d3326, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27093 (p : Pattern) (guard : d5269 p = 1) : d3327 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3327, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27092 p hg
    simpa only [d3327, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3327, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27003 p hg
    simpa only [d3327, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27094 (p : Pattern) (guard : d5269 p = 1) : d3328 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3328, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27093 p hg
    simpa only [d3328, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3328, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27032 p hg
    simpa only [d3328, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27095 (p : Pattern) (guard : d5269 p = 1) : d3329 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3329, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27074 p hg
    simpa only [d3329, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3329, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27062 p hg
    simpa only [d3329, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27096 (p : Pattern) (guard : d5269 p = 1) : d3330 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3330, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27094 p hg
    simpa only [d3330, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3330, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27095 p hg
    simpa only [d3330, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27097 (p : Pattern) (guard : d5269 p = 1) : d3331 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3331, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27096 p hg
    simpa only [d3331, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3331, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27079 p hg
    simpa only [d3331, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27098 (p : Pattern) (guard : d5269 p = 1) : d3332 p ≤ (2 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3332, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27079 p hg
    simpa only [d3332, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3332, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3332, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27099 (p : Pattern) (guard : d5269 p = 1) : d3333 p ≤ (2 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3333, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27097 p hg
    simpa only [d3333, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3333, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27098 p hg
    simpa only [d3333, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27100 (p : Pattern) (guard : d5269 p = 1) : d3334 p ≤ (2 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3334, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27090 p hg
    simpa only [d3334, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3334, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27099 p hg
    simpa only [d3334, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27101 (p : Pattern) (guard : d0 p = 1) : d3336 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27102 (p : Pattern) (guard : d5269 p = 1) : d3337 p ≤ (2 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, d3337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27101 p hg
    simpa only [d5269, d3337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, d3337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26974 p hg
    simpa only [d5269, d3337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27103 (p : Pattern) (guard : d5269 p = 1) : d3338 p ≤ (2 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27102 p hg
    simpa only [d3338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26977 p hg
    simpa only [d3338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27104 (p : Pattern) (guard : d5269 p = 1) : d3339 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3339, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27103 p hg
    simpa only [d3339, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3339, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26980 p hg
    simpa only [d3339, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27105 (p : Pattern) (guard : d5269 p = 1) : d3340 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27104 p hg
    simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26987 p hg
    simpa only [d3340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27106 (p : Pattern) (guard : d5269 p = 1) : d3341 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3341, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27105 p hg
    simpa only [d3341, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3341, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26994 p hg
    simpa only [d3341, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27107 (p : Pattern) (guard : d5269 p = 1) : d3342 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3342, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27106 p hg
    simpa only [d3342, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3342, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27003 p hg
    simpa only [d3342, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27108 (p : Pattern) (guard : d5269 p = 1) : d3343 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3343, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27107 p hg
    simpa only [d3343, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3343, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27032 p hg
    simpa only [d3343, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27109 (p : Pattern) (guard : d5269 p = 1) : d3344 p ≤ (2 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3344, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26985 p hg
    simpa only [d3344, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3344, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27038 p hg
    simpa only [d3344, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27110 (p : Pattern) (guard : d5269 p = 1) : d3345 p ≤ (2 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3345, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27109 p hg
    simpa only [d3345, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3345, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27040 p hg
    simpa only [d3345, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27111 (p : Pattern) (guard : d5269 p = 1) : d3346 p ≤ (2 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3346, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27110 p hg
    simpa only [d3346, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3346, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27051 p hg
    simpa only [d3346, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27112 (p : Pattern) (guard : d5269 p = 1) : d3347 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3347, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27111 p hg
    simpa only [d3347, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3347, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27062 p hg
    simpa only [d3347, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27113 (p : Pattern) (guard : d5269 p = 1) : d3348 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3348, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27108 p hg
    simpa only [d3348, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3348, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27112 p hg
    simpa only [d3348, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27114 (p : Pattern) (guard : d5269 p = 1) : d3349 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3349, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27113 p hg
    simpa only [d3349, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3349, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27079 p hg
    simpa only [d3349, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27115 (p : Pattern) (guard : d5269 p = 1) : d3350 p ≤ (2 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3350, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27114 p hg
    simpa only [d3350, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3350, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27089 p hg
    simpa only [d3350, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27116 (p : Pattern) (guard : d5269 p = 1) : d3351 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3351, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27066 p hg
    simpa only [d3351, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3351, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27032 p hg
    simpa only [d3351, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27117 (p : Pattern) (guard : d5269 p = 1) : d3352 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3352, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27116 p hg
    simpa only [d3352, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3352, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27095 p hg
    simpa only [d3352, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27118 (p : Pattern) (guard : d5269 p = 1) : d3353 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3353, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27117 p hg
    simpa only [d3353, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3353, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27079 p hg
    simpa only [d3353, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27119 (p : Pattern) (guard : d5269 p = 1) : d3354 p ≤ (2 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3354, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27118 p hg
    simpa only [d3354, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3354, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27098 p hg
    simpa only [d3354, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27120 (p : Pattern) (guard : d5269 p = 1) : d3355 p ≤ (2 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3355, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27115 p hg
    simpa only [d3355, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3355, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27119 p hg
    simpa only [d3355, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27121 (p : Pattern) (guard : d5269 p = 1) : d3356 p ≤ (2 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27100 p hg
    simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27120 p hg
    simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27122 (p : Pattern) (guard : d0 p = 1) : d3359 p ≤ (2 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27123 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27124 (p : Pattern) (guard : d5268 p = 1) : d3358 p ≤ (2 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3358, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15921 p hg
    simpa only [d5268, d3358, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3358, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27123 p hg
    simpa only [d5268, d3358, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27125 (p : Pattern) (guard : d5269 p = 1) : d3360 p ≤ (2 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, d3360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27122 p hg
    simpa only [d5269, d3360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, d3360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27124 p hg
    simpa only [d5269, d3360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27126 (p : Pattern) (guard : d0 p = 1) : d3358 p ≤ (2 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27127 (p : Pattern) (guard : d5269 p = 1) : d3358 p ≤ (2 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27126 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27124 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27128 (p : Pattern) (guard : d5269 p = 1) : d3361 p ≤ (2 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27125 p hg
    simpa only [d3361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27127 p hg
    simpa only [d3361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27129 (p : Pattern) (guard : d5269 p = 1) : d3362 p ≤ (2 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3362, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27127 p hg
    simpa only [d3362, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3362, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3362, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27130 (p : Pattern) (guard : d5269 p = 1) : d3363 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3363, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27128 p hg
    simpa only [d3363, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3363, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27129 p hg
    simpa only [d3363, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27131 (p : Pattern) (guard : d5269 p = 1) : d3364 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3364, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27127 p hg
    simpa only [d3364, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3364, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27129 p hg
    simpa only [d3364, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27132 (p : Pattern) (guard : d5269 p = 1) : d3365 p ≤ (2 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27130 p hg
    simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27131 p hg
    simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27133 (p : Pattern) (guard : d0 p = 1) : d3366 p ≤ (2 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27134 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d106 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27135 (p : Pattern) (guard : d5268 p = 1) : d3366 p ≤ (2 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3366, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15933 p hg
    simpa only [d5268, d3366, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3366, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27134 p hg
    simpa only [d5268, d3366, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27136 (p : Pattern) (guard : d5269 p = 1) : d3366 p ≤ (2 : Int) + d107 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27133 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27135 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27137 (p : Pattern) (guard : d5269 p = 1) : d3367 p ≤ (2 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3367, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27136 p hg
    simpa only [d3367, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3367, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3367, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27138 (p : Pattern) (guard : d5269 p = 1) : d3368 p ≤ (2 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3368, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27136 p hg
    simpa only [d3368, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3368, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27137 p hg
    simpa only [d3368, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27139 (p : Pattern) (guard : d5269 p = 1) : d3369 p ≤ (2 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3369, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27131 p hg
    simpa only [d3369, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3369, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27138 p hg
    simpa only [d3369, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27140 (p : Pattern) (guard : d5269 p = 1) : d3370 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3370, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27132 p hg
    simpa only [d3370, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3370, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27139 p hg
    simpa only [d3370, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27141 (p : Pattern) (guard : d5269 p = 1) : d3371 p ≤ (2 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3371, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27047 p hg
    simpa only [d3371, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3371, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3371, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27142 (p : Pattern) (guard : d5269 p = 1) : d3372 p ≤ (2 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3372, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27139 p hg
    simpa only [d3372, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3372, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27141 p hg
    simpa only [d3372, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27143 (p : Pattern) (guard : d5269 p = 1) : d3373 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3373, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27140 p hg
    simpa only [d3373, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3373, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27142 p hg
    simpa only [d3373, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27144 (p : Pattern) (guard : d0 p = 1) : d3374 p ≤ (2 : Int) + d116 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27145 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27146 (p : Pattern) (guard : d5268 p = 1) : d3374 p ≤ (2 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3374, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15951 p hg
    simpa only [d5268, d3374, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3374, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27145 p hg
    simpa only [d5268, d3374, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27147 (p : Pattern) (guard : d5269 p = 1) : d3374 p ≤ (2 : Int) + d116 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27144 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27146 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27148 (p : Pattern) (guard : d5269 p = 1) : d3375 p ≤ (2 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3375, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27147 p hg
    simpa only [d3375, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3375, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3375, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27149 (p : Pattern) (guard : d5269 p = 1) : d3376 p ≤ (2 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3376, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27127 p hg
    simpa only [d3376, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3376, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27148 p hg
    simpa only [d3376, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27150 (p : Pattern) (guard : d0 p = 1) : d3377 p ≤ (2 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27151 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d119 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27152 (p : Pattern) (guard : d5268 p = 1) : d3377 p ≤ (2 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d3377, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15979 p hg
    simpa only [d5268, d3377, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d3377, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27151 p hg
    simpa only [d5268, d3377, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27153 (p : Pattern) (guard : d5269 p = 1) : d3377 p ≤ (2 : Int) + d120 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27150 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27152 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27154 (p : Pattern) (guard : d5269 p = 1) : d3378 p ≤ (2 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3378, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27153 p hg
    simpa only [d3378, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3378, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3378, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27155 (p : Pattern) (guard : d5269 p = 1) : d3379 p ≤ (2 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3379, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27127 p hg
    simpa only [d3379, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3379, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27154 p hg
    simpa only [d3379, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27156 (p : Pattern) (guard : d5269 p = 1) : d3380 p ≤ (2 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3380, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27149 p hg
    simpa only [d3380, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3380, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27155 p hg
    simpa only [d3380, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27157 (p : Pattern) (guard : d5269 p = 1) : d3381 p ≤ (2 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3381, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27127 p hg
    simpa only [d3381, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3381, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3381, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27158 (p : Pattern) (guard : d5269 p = 1) : d3382 p ≤ (2 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3382, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27136 p hg
    simpa only [d3382, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3382, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3382, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27159 (p : Pattern) (guard : d5269 p = 1) : d3383 p ≤ (2 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3383, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27157 p hg
    simpa only [d3383, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3383, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27158 p hg
    simpa only [d3383, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
