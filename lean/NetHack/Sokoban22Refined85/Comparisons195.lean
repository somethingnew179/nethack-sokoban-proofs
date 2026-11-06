/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons194
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare27300 (p : Pattern) (guard : d5269 p = 1) : d3522 p ≤ (2 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3522, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27294 p hg
    simpa only [d3522, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3522, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27299 p hg
    simpa only [d3522, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27301 (p : Pattern) (guard : d5269 p = 1) : d3523 p ≤ (2 : Int) + d251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3523, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27290 p hg
    simpa only [d3523, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3523, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27300 p hg
    simpa only [d3523, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27302 (p : Pattern) (guard : d5269 p = 1) : d3524 p ≤ (2 : Int) + d252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3524, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27169 p hg
    simpa only [d3524, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3524, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27001 p hg
    simpa only [d3524, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27303 (p : Pattern) (guard : d5269 p = 1) : d3525 p ≤ (2 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3525, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27131 p hg
    simpa only [d3525, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3525, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27302 p hg
    simpa only [d3525, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27304 (p : Pattern) (guard : d5269 p = 1) : d3526 p ≤ (2 : Int) + d254 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3526, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27138 p hg
    simpa only [d3526, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3526, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27001 p hg
    simpa only [d3526, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27305 (p : Pattern) (guard : d5269 p = 1) : d3527 p ≤ (2 : Int) + d255 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3527, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27304 p hg
    simpa only [d3527, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3527, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3527, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27306 (p : Pattern) (guard : d5269 p = 1) : d3528 p ≤ (2 : Int) + d256 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3528, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27303 p hg
    simpa only [d3528, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3528, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27305 p hg
    simpa only [d3528, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27307 (p : Pattern) (guard : d5269 p = 1) : d3529 p ≤ (2 : Int) + d257 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3529, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27187 p hg
    simpa only [d3529, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3529, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27049 p hg
    simpa only [d3529, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27308 (p : Pattern) (guard : d5269 p = 1) : d3530 p ≤ (2 : Int) + d258 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3530, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27307 p hg
    simpa only [d3530, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3530, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3530, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27309 (p : Pattern) (guard : d5269 p = 1) : d3531 p ≤ (2 : Int) + d259 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3531, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27308 p hg
    simpa only [d3531, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3531, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3531, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27310 (p : Pattern) (guard : d5269 p = 1) : d3532 p ≤ (2 : Int) + d260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3532, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27306 p hg
    simpa only [d3532, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3532, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27309 p hg
    simpa only [d3532, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27311 (p : Pattern) (guard : d5269 p = 1) : d3533 p ≤ (2 : Int) + d261 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3533, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27310 p hg
    simpa only [d3533, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3533, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27299 p hg
    simpa only [d3533, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27312 (p : Pattern) (guard : d5269 p = 1) : d3534 p ≤ (2 : Int) + d262 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3534, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27311 p hg
    simpa only [d3534, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3534, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d3534, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27313 (p : Pattern) (guard : d5269 p = 1) : d3535 p ≤ (2 : Int) + d263 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3535, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27301 p hg
    simpa only [d3535, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3535, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27312 p hg
    simpa only [d3535, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27314 (p : Pattern) (guard : d5269 p = 1) : d3536 p ≤ (2 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3536, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27275 p hg
    simpa only [d3536, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3536, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27313 p hg
    simpa only [d3536, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27315 (p : Pattern) (guard : d5269 p = 1) : d3537 p ≤ (2 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3537, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27100 p hg
    simpa only [d3537, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3537, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27314 p hg
    simpa only [d3537, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27316 (p : Pattern) (guard : d5269 p = 1) : d3538 p ≤ (2 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3538, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27258 p hg
    simpa only [d3538, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3538, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27315 p hg
    simpa only [d3538, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27317 (p : Pattern) (guard : d5269 p = 1) : d3539 p ≤ (2 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d3539, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27215 p hg
    simpa only [d3539, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d3539, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27316 p hg
    simpa only [d3539, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27318 (p : Pattern) (guard : d5847 p = 1) : d3225 p ≤ (0 : Int) + d3540 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3225, d3540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19825 p hg
    simpa only [d5847, d3225, d3540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3225, d3540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26603 p hg
    simpa only [d5847, d3225, d3540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27319 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d13 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19829 p hg
    simpa only [d5847, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19882 p hg
    simpa only [d5847, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27320 (p : Pattern) (guard : d5847 p = 1) : d3227 p ≤ (0 : Int) + d3541 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3227, d3541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27318 p hg
    simpa only [d3227, d3541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3227, d3541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d3227, d3541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27321 (p : Pattern) (guard : d5847 p = 1) : d3228 p ≤ (0 : Int) + d3542 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3228, d3542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27320 p hg
    simpa only [d3228, d3542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3228, d3542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d3228, d3542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27322 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3543 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3226, d3543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19829 p hg
    simpa only [d5847, d3226, d3543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3226, d3543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19865 p hg
    simpa only [d5847, d3226, d3543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27323 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3544 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27322 p hg
    simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27324 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3545 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27323 p hg
    simpa only [d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27322 p hg
    simpa only [d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27325 (p : Pattern) (guard : d5847 p = 1) : d3229 p ≤ (0 : Int) + d3546 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3229, d3546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27321 p hg
    simpa only [d3229, d3546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3229, d3546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27324 p hg
    simpa only [d3229, d3546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27326 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3547 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3226, d3547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19829 p hg
    simpa only [d5847, d3226, d3547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3226, d3547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19972 p hg
    simpa only [d5847, d3226, d3547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27327 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3548 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27326 p hg
    simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27328 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3549 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27327 p hg
    simpa only [d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27326 p hg
    simpa only [d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27329 (p : Pattern) (guard : d5847 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare27330 (p : Pattern) (guard : d5847 p = 1) : d3230 p ≤ (0 : Int) + d3550 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3230, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27328 p hg
    simpa only [d3230, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3230, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3230, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27331 (p : Pattern) (guard : d5847 p = 1) : d3231 p ≤ (0 : Int) + d3551 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3231, d3551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27325 p hg
    simpa only [d3231, d3551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3231, d3551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27330 p hg
    simpa only [d3231, d3551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27332 (p : Pattern) (guard : d5847 p = 1) : d3232 p ≤ (0 : Int) + d13 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19829 p hg
    simpa only [d5847, d3232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26614 p hg
    simpa only [d5847, d3232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27333 (p : Pattern) (guard : d5847 p = 1) : d3233 p ≤ (0 : Int) + d13 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27332 p hg
    simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27334 (p : Pattern) (guard : d5847 p = 1) : d3234 p ≤ (0 : Int) + d13 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27333 p hg
    simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27335 (p : Pattern) (guard : d5847 p = 1) : d3235 p ≤ (0 : Int) + d3552 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3235, d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27334 p hg
    simpa only [d3235, d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3235, d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27324 p hg
    simpa only [d3235, d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27336 (p : Pattern) (guard : d5847 p = 1) : d3236 p ≤ (0 : Int) + d3553 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3236, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27335 p hg
    simpa only [d3236, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3236, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27330 p hg
    simpa only [d3236, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27337 (p : Pattern) (guard : d5847 p = 1) : d3237 p ≤ (0 : Int) + d3554 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3237, d3554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27331 p hg
    simpa only [d3237, d3554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3237, d3554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27336 p hg
    simpa only [d3237, d3554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27338 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3552 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27324 p hg
    simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27339 (p : Pattern) (guard : d5847 p = 1) : d3238 p ≤ (0 : Int) + d3553 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3238, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27338 p hg
    simpa only [d3238, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3238, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27330 p hg
    simpa only [d3238, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27340 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d17 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19860 p hg
    simpa only [d5847, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19865 p hg
    simpa only [d5847, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27341 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d3555 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3239, d3555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19860 p hg
    simpa only [d5847, d3239, d3555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3239, d3555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20382 p hg
    simpa only [d5847, d3239, d3555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27342 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d3556 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27340 p hg
    simpa only [d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27341 p hg
    simpa only [d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27343 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d3557 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27342 p hg
    simpa only [d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27341 p hg
    simpa only [d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27344 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d3558 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27340 p hg
    simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27343 p hg
    simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27345 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d3559 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3239, d3559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19860 p hg
    simpa only [d5847, d3239, d3559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3239, d3559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20051 p hg
    simpa only [d5847, d3239, d3559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27346 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d3560 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27340 p hg
    simpa only [d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27345 p hg
    simpa only [d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27347 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d3561 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27346 p hg
    simpa only [d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27345 p hg
    simpa only [d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27348 (p : Pattern) (guard : d5847 p = 1) : d3240 p ≤ (0 : Int) + d3562 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3240, d3562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27347 p hg
    simpa only [d3240, d3562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3240, d3562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3240, d3562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27349 (p : Pattern) (guard : d5847 p = 1) : d3241 p ≤ (0 : Int) + d3563 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3241, d3563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27344 p hg
    simpa only [d3241, d3563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3241, d3563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27348 p hg
    simpa only [d3241, d3563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27350 (p : Pattern) (guard : d5847 p = 1) : d3242 p ≤ (0 : Int) + d3564 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3242, d3564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27339 p hg
    simpa only [d3242, d3564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3242, d3564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27349 p hg
    simpa only [d3242, d3564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27351 (p : Pattern) (guard : d5847 p = 1) : d3243 p ≤ (0 : Int) + d3565 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3243, d3565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27337 p hg
    simpa only [d3243, d3565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3243, d3565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27350 p hg
    simpa only [d3243, d3565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27352 (p : Pattern) (guard : d5847 p = 1) : d3244 p ≤ (0 : Int) + d23 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19888 p hg
    simpa only [d5847, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19893 p hg
    simpa only [d5847, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27353 (p : Pattern) (guard : d5847 p = 1) : d3244 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3244, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19888 p hg
    simpa only [d5847, d3244, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3244, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3244, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27354 (p : Pattern) (guard : d5847 p = 1) : d3244 p ≤ (0 : Int) + d3566 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27352 p hg
    simpa only [d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27353 p hg
    simpa only [d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27355 (p : Pattern) (guard : d5847 p = 1) : d3244 p ≤ (0 : Int) + d3567 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27354 p hg
    simpa only [d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27353 p hg
    simpa only [d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27356 (p : Pattern) (guard : d5847 p = 1) : d3244 p ≤ (0 : Int) + d3568 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27352 p hg
    simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27355 p hg
    simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27357 (p : Pattern) (guard : d5847 p = 1) : d3244 p ≤ (0 : Int) + d3569 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3244, d3569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19888 p hg
    simpa only [d5847, d3244, d3569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3244, d3569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20007 p hg
    simpa only [d5847, d3244, d3569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27358 (p : Pattern) (guard : d5847 p = 1) : d3244 p ≤ (0 : Int) + d3570 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27352 p hg
    simpa only [d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27357 p hg
    simpa only [d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27359 (p : Pattern) (guard : d5847 p = 1) : d3244 p ≤ (0 : Int) + d3571 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27358 p hg
    simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27357 p hg
    simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27360 (p : Pattern) (guard : d5847 p = 1) : d3245 p ≤ (0 : Int) + d3572 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3245, d3572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27359 p hg
    simpa only [d3245, d3572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3245, d3572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3245, d3572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27361 (p : Pattern) (guard : d5847 p = 1) : d3246 p ≤ (0 : Int) + d3573 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3246, d3573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27356 p hg
    simpa only [d3246, d3573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3246, d3573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27360 p hg
    simpa only [d3246, d3573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27362 (p : Pattern) (guard : d5847 p = 1) : d3247 p ≤ (0 : Int) + d3574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3247, d3574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27361 p hg
    simpa only [d3247, d3574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3247, d3574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3247, d3574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27363 (p : Pattern) (guard : d5847 p = 1) : d3248 p ≤ (0 : Int) + d3575 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3248, d3575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27350 p hg
    simpa only [d3248, d3575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3248, d3575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27362 p hg
    simpa only [d3248, d3575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27364 (p : Pattern) (guard : d5847 p = 1) : d3249 p ≤ (0 : Int) + d3576 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3249, d3576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27351 p hg
    simpa only [d3249, d3576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3249, d3576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27363 p hg
    simpa only [d3249, d3576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27365 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3577 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3226, d3577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19829 p hg
    simpa only [d5847, d3226, d3577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3226, d3577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20051 p hg
    simpa only [d5847, d3226, d3577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27366 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3578 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27365 p hg
    simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27367 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3579 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3226, d3579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19829 p hg
    simpa only [d5847, d3226, d3579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3226, d3579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19893 p hg
    simpa only [d5847, d3226, d3579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27368 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3580 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27322 p hg
    simpa only [d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27367 p hg
    simpa only [d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27369 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3581 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27366 p hg
    simpa only [d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27368 p hg
    simpa only [d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27370 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d3582 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27369 p hg
    simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27371 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d30 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19916 p hg
    simpa only [d5847, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19972 p hg
    simpa only [d5847, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27372 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3583 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3250, d3583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19916 p hg
    simpa only [d5847, d3250, d3583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3250, d3583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20382 p hg
    simpa only [d5847, d3250, d3583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27373 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3584 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27371 p hg
    simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27372 p hg
    simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27374 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3585 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3250, d3585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19916 p hg
    simpa only [d5847, d3250, d3585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3250, d3585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20051 p hg
    simpa only [d5847, d3250, d3585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27375 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d1715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3250, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19916 p hg
    simpa only [d5847, d3250, d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3250, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20007 p hg
    simpa only [d5847, d3250, d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27376 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3586 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27374 p hg
    simpa only [d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27375 p hg
    simpa only [d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27377 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3587 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27373 p hg
    simpa only [d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27376 p hg
    simpa only [d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27378 (p : Pattern) (guard : d5847 p = 1) : d3251 p ≤ (0 : Int) + d3588 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3251, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27377 p hg
    simpa only [d3251, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3251, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3251, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27379 (p : Pattern) (guard : d5847 p = 1) : d3252 p ≤ (0 : Int) + d3589 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3252, d3589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27370 p hg
    simpa only [d3252, d3589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3252, d3589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27378 p hg
    simpa only [d3252, d3589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27380 (p : Pattern) (guard : d5847 p = 1) : d3253 p ≤ (0 : Int) + d34 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19927 p hg
    simpa only [d5847, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20051 p hg
    simpa only [d5847, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27381 (p : Pattern) (guard : d5847 p = 1) : d3253 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3253, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19927 p hg
    simpa only [d5847, d3253, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3253, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3253, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27382 (p : Pattern) (guard : d5847 p = 1) : d3253 p ≤ (0 : Int) + d3590 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27380 p hg
    simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27381 p hg
    simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27383 (p : Pattern) (guard : d5847 p = 1) : d3253 p ≤ (0 : Int) + d3591 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3253, d3591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19927 p hg
    simpa only [d5847, d3253, d3591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3253, d3591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19996 p hg
    simpa only [d5847, d3253, d3591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27384 (p : Pattern) (guard : d5847 p = 1) : d3253 p ≤ (0 : Int) + d3592 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27383 p hg
    simpa only [d3592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27381 p hg
    simpa only [d3592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27385 (p : Pattern) (guard : d5847 p = 1) : d3253 p ≤ (0 : Int) + d3593 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27382 p hg
    simpa only [d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27384 p hg
    simpa only [d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27386 (p : Pattern) (guard : d5847 p = 1) : d3254 p ≤ (0 : Int) + d3594 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3254, d3594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27385 p hg
    simpa only [d3254, d3594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3254, d3594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3254, d3594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27387 (p : Pattern) (guard : d5847 p = 1) : d3255 p ≤ (0 : Int) + d3595 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3255, d3595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27370 p hg
    simpa only [d3255, d3595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3255, d3595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27386 p hg
    simpa only [d3255, d3595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27388 (p : Pattern) (guard : d5847 p = 1) : d3256 p ≤ (0 : Int) + d3596 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3256, d3596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27379 p hg
    simpa only [d3256, d3596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3256, d3596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27387 p hg
    simpa only [d3256, d3596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27389 (p : Pattern) (guard : d5847 p = 1) : d3257 p ≤ (0 : Int) + d39 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19938 p hg
    simpa only [d5847, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20007 p hg
    simpa only [d5847, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27390 (p : Pattern) (guard : d5847 p = 1) : d3257 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3257, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19938 p hg
    simpa only [d5847, d3257, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3257, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3257, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27391 (p : Pattern) (guard : d5847 p = 1) : d3257 p ≤ (0 : Int) + d3597 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27389 p hg
    simpa only [d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27390 p hg
    simpa only [d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27392 (p : Pattern) (guard : d5847 p = 1) : d3257 p ≤ (0 : Int) + d3598 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27391 p hg
    simpa only [d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27390 p hg
    simpa only [d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27393 (p : Pattern) (guard : d5847 p = 1) : d3258 p ≤ (0 : Int) + d3599 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3258, d3599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27392 p hg
    simpa only [d3258, d3599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3258, d3599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3258, d3599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27394 (p : Pattern) (guard : d5847 p = 1) : d3259 p ≤ (0 : Int) + d3600 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3259, d3600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27370 p hg
    simpa only [d3259, d3600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3259, d3600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27393 p hg
    simpa only [d3259, d3600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27395 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d3601 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3239, d3601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19860 p hg
    simpa only [d5847, d3239, d3601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3239, d3601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19996 p hg
    simpa only [d5847, d3239, d3601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27396 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d3602 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27340 p hg
    simpa only [d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27395 p hg
    simpa only [d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27397 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d339 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3239, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19860 p hg
    simpa only [d5847, d3239, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3239, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3239, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27398 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d3603 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27341 p hg
    simpa only [d3603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27397 p hg
    simpa only [d3603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27399 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d3604 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27396 p hg
    simpa only [d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27398 p hg
    simpa only [d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27400 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d3605 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27340 p hg
    simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27401 (p : Pattern) (guard : d5847 p = 1) : d3260 p ≤ (0 : Int) + d3606 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3260, d3606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27400 p hg
    simpa only [d3260, d3606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3260, d3606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3260, d3606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27402 (p : Pattern) (guard : d5847 p = 1) : d3261 p ≤ (0 : Int) + d3607 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3261, d3607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27394 p hg
    simpa only [d3261, d3607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3261, d3607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d3261, d3607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27403 (p : Pattern) (guard : d5847 p = 1) : d3262 p ≤ (0 : Int) + d3608 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3262, d3608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27388 p hg
    simpa only [d3262, d3608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3262, d3608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27402 p hg
    simpa only [d3262, d3608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27404 (p : Pattern) (guard : d5847 p = 1) : d3263 p ≤ (0 : Int) + d3609 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3263, d3609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27370 p hg
    simpa only [d3263, d3609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3263, d3609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3263, d3609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27405 (p : Pattern) (guard : d5847 p = 1) : d3264 p ≤ (0 : Int) + d3610 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3264, d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27404 p hg
    simpa only [d3264, d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3264, d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d3264, d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27406 (p : Pattern) (guard : d5847 p = 1) : d3265 p ≤ (0 : Int) + d3611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3265, d3611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27356 p hg
    simpa only [d3265, d3611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3265, d3611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3265, d3611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27407 (p : Pattern) (guard : d5847 p = 1) : d3266 p ≤ (0 : Int) + d3612 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3266, d3612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d3266, d3612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3266, d3612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3266, d3612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27408 (p : Pattern) (guard : d5847 p = 1) : d3267 p ≤ (0 : Int) + d3613 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3267, d3613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d3267, d3613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3267, d3613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d3267, d3613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27409 (p : Pattern) (guard : d5847 p = 1) : d3268 p ≤ (0 : Int) + d3614 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3268, d3614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d3268, d3614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3268, d3614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27408 p hg
    simpa only [d3268, d3614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27410 (p : Pattern) (guard : d5847 p = 1) : d3269 p ≤ (0 : Int) + d3615 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3269, d3615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27364 p hg
    simpa only [d3269, d3615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3269, d3615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27409 p hg
    simpa only [d3269, d3615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27411 (p : Pattern) (guard : d5847 p = 1) : d3270 p ≤ (0 : Int) + d3616 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3270, d3616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19963 p hg
    simpa only [d5847, d3270, d3616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3270, d3616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26669 p hg
    simpa only [d5847, d3270, d3616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27412 (p : Pattern) (guard : d5847 p = 1) : d3271 p ≤ (0 : Int) + d3617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3271, d3617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d3271, d3617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3271, d3617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d3271, d3617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27413 (p : Pattern) (guard : d5847 p = 1) : d3272 p ≤ (0 : Int) + d3618 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3272, d3618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27412 p hg
    simpa only [d3272, d3618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3272, d3618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27319 p hg
    simpa only [d3272, d3618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27414 (p : Pattern) (guard : d5847 p = 1) : d3273 p ≤ (0 : Int) + d3619 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3273, d3619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27413 p hg
    simpa only [d3273, d3619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3273, d3619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27324 p hg
    simpa only [d3273, d3619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27415 (p : Pattern) (guard : d5847 p = 1) : d3274 p ≤ (0 : Int) + d3620 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3274, d3620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27414 p hg
    simpa only [d3274, d3620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3274, d3620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27330 p hg
    simpa only [d3274, d3620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27416 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3621 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27371 p hg
    simpa only [d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27374 p hg
    simpa only [d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27417 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3622 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27416 p hg
    simpa only [d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27374 p hg
    simpa only [d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27418 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3623 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27371 p hg
    simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27417 p hg
    simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27419 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3624 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3250, d3624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19916 p hg
    simpa only [d5847, d3250, d3624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3250, d3624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19865 p hg
    simpa only [d5847, d3250, d3624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27420 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3625 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27371 p hg
    simpa only [d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27421 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d3626 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27420 p hg
    simpa only [d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27422 (p : Pattern) (guard : d5847 p = 1) : d3251 p ≤ (0 : Int) + d3627 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3251, d3627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27421 p hg
    simpa only [d3251, d3627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3251, d3627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3251, d3627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27423 (p : Pattern) (guard : d5847 p = 1) : d3275 p ≤ (0 : Int) + d3628 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3275, d3628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27418 p hg
    simpa only [d3275, d3628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3275, d3628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27422 p hg
    simpa only [d3275, d3628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27424 (p : Pattern) (guard : d5847 p = 1) : d3276 p ≤ (0 : Int) + d3629 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3276, d3629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27415 p hg
    simpa only [d3276, d3629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3276, d3629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d3276, d3629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27425 (p : Pattern) (guard : d5847 p = 1) : d3277 p ≤ (0 : Int) + d3630 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3277, d3630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27349 p hg
    simpa only [d3277, d3630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3277, d3630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27361 p hg
    simpa only [d3277, d3630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27426 (p : Pattern) (guard : d5847 p = 1) : d3278 p ≤ (0 : Int) + d3631 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3278, d3631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27424 p hg
    simpa only [d3278, d3631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3278, d3631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d3278, d3631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27427 (p : Pattern) (guard : d5847 p = 1) : d3279 p ≤ (0 : Int) + d57 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19991 p hg
    simpa only [d5847, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19996 p hg
    simpa only [d5847, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27428 (p : Pattern) (guard : d5847 p = 1) : d3279 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3279, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19991 p hg
    simpa only [d5847, d3279, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3279, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3279, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27429 (p : Pattern) (guard : d5847 p = 1) : d3279 p ≤ (0 : Int) + d3632 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27427 p hg
    simpa only [d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27430 (p : Pattern) (guard : d5847 p = 1) : d3279 p ≤ (0 : Int) + d3633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27429 p hg
    simpa only [d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27431 (p : Pattern) (guard : d5847 p = 1) : d3279 p ≤ (0 : Int) + d3634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27427 p hg
    simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27432 (p : Pattern) (guard : d5847 p = 1) : d3280 p ≤ (0 : Int) + d3635 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3280, d3635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d3280, d3635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3280, d3635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3280, d3635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27433 (p : Pattern) (guard : d5847 p = 1) : d3281 p ≤ (0 : Int) + d3636 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3281, d3636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27431 p hg
    simpa only [d3281, d3636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3281, d3636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27432 p hg
    simpa only [d3281, d3636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27434 (p : Pattern) (guard : d5847 p = 1) : d3282 p ≤ (0 : Int) + d3637 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3282, d3637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27349 p hg
    simpa only [d3282, d3637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3282, d3637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27433 p hg
    simpa only [d3282, d3637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27435 (p : Pattern) (guard : d5847 p = 1) : d3257 p ≤ (0 : Int) + d3638 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27389 p hg
    simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27392 p hg
    simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27436 (p : Pattern) (guard : d5847 p = 1) : d3283 p ≤ (0 : Int) + d3639 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3283, d3639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27435 p hg
    simpa only [d3283, d3639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3283, d3639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27393 p hg
    simpa only [d3283, d3639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27437 (p : Pattern) (guard : d5847 p = 1) : d3284 p ≤ (0 : Int) + d3640 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3284, d3640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d3284, d3640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3284, d3640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3284, d3640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27438 (p : Pattern) (guard : d5847 p = 1) : d3285 p ≤ (0 : Int) + d3641 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3285, d3641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27434 p hg
    simpa only [d3285, d3641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3285, d3641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27437 p hg
    simpa only [d3285, d3641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27439 (p : Pattern) (guard : d5847 p = 1) : d3286 p ≤ (0 : Int) + d3642 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3286, d3642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27426 p hg
    simpa only [d3286, d3642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3286, d3642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27438 p hg
    simpa only [d3286, d3642, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
