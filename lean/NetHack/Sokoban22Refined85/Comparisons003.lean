/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare420 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare387 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare419 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare421 (p : Pattern) (guard : d1 p = 1) : d83 p ≤ (1 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d83, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare397 p hg
    simpa only [d83, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d83, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare420 p hg
    simpa only [d83, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare422 (p : Pattern) (guard : d1 p = 1) : d84 p ≤ (1 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d84, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare421 p hg
    simpa only [d84, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d84, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d84, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare423 (p : Pattern) (guard : d1 p = 1) : d200 p ≤ (1 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d200, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d200, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d200, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare422 p hg
    simpa only [d200, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare424 (p : Pattern) (guard : d1 p = 1) : d201 p ≤ (1 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d201, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare411 p hg
    simpa only [d201, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d201, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d201, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare425 (p : Pattern) (guard : d1 p = 1) : d202 p ≤ (1 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d202, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare424 p hg
    simpa only [d202, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d202, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d202, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare426 (p : Pattern) (guard : d1 p = 1) : d203 p ≤ (1 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d203, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare425 p hg
    simpa only [d203, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d203, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d203, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare427 (p : Pattern) (guard : d1 p = 1) : d204 p ≤ (1 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d204, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare423 p hg
    simpa only [d204, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d204, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare426 p hg
    simpa only [d204, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare428 (p : Pattern) (guard : d1 p = 1) : d205 p ≤ (1 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d205, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare415 p hg
    simpa only [d205, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d205, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare427 p hg
    simpa only [d205, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare429 (p : Pattern) (guard : d1 p = 1) : d206 p ≤ (1 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d206, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare393 p hg
    simpa only [d206, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d206, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare428 p hg
    simpa only [d206, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare430 (p : Pattern) (guard : d1 p = 1) : d207 p ≤ (1 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d207, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare428 p hg
    simpa only [d207, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d207, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d207, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare431 (p : Pattern) (guard : d1 p = 1) : d208 p ≤ (1 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d208, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare429 p hg
    simpa only [d208, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d208, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare430 p hg
    simpa only [d208, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare432 (p : Pattern) (guard : d1 p = 1) : d209 p ≤ (1 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d209, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare354 p hg
    simpa only [d209, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d209, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare431 p hg
    simpa only [d209, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare433 (p : Pattern) (guard : d1 p = 1) : d210 p ≤ (1 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d210, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d210, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d210, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare432 p hg
    simpa only [d210, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare434 (p : Pattern) (guard : d0 p = 1) : d265 p ≤ (1 : Int) + d168 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare435 (p : Pattern) (guard : d4040 p = 1) : d266 p ≤ (1 : Int) + d168 p := by
  cases selected : p 49 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4040, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare433 p hg
    simpa only [d4040, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4040, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare434 p hg
    simpa only [d4040, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare436 (p : Pattern) (guard : d4045 p = 1) : d267 p ≤ (1 : Int) + d168 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4045, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare269 p hg
    simpa only [d4045, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4040 p = 1 := by simpa only [d4045, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare435 p hg
    simpa only [d4045, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare437 (p : Pattern) (guard : d0 p = 1) : d480 p ≤ (0 : Int) + d266 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare438 (p : Pattern) (guard : d4038 p = 1) : d481 p ≤ (0 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4038, d481, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2 p hg
    simpa only [d4038, d481, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4038, d481, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare437 p hg
    simpa only [d4038, d481, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare439 (p : Pattern) (guard : d0 p = 1) : d480 p ≤ (0 : Int) + d483 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare440 (p : Pattern) (guard : d4044 p = 1) : d481 p ≤ (0 : Int) + d484 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4040 p = 1 := by simpa only [d4044, d481, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7 p hg
    simpa only [d4044, d481, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4044, d481, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare439 p hg
    simpa only [d4044, d481, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare441 (p : Pattern) (guard : d0 p = 1) : d101 p ≤ (1 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare442 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (1 : Int) + d0 p := by
  change (1 : Int) ≤ (1 : Int) + 0
  decide
theorem compare443 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (1 : Int) + d13 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare442 p hg
    simpa only [d102, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d102, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare444 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (1 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare442 p hg
    simpa only [d103, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare443 p hg
    simpa only [d103, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare445 (p : Pattern) (guard : d1 p = 1) : d104 p ≤ (1 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d104, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare444 p hg
    simpa only [d104, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d104, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d104, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare446 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (1 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare444 p hg
    simpa only [d105, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare445 p hg
    simpa only [d105, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare447 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (1 : Int) + d4 p := by
  change (5 : Int) ≤ (1 : Int) + 4
  decide
theorem compare448 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (1 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare447 p hg
    simpa only [d106, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d106, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare449 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (1 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare447 p hg
    simpa only [d107, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare448 p hg
    simpa only [d107, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare450 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (1 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d108, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare449 p hg
    simpa only [d108, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d108, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d108, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare451 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (1 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare449 p hg
    simpa only [d109, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare450 p hg
    simpa only [d109, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare452 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (1 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare446 p hg
    simpa only [d110, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare451 p hg
    simpa only [d110, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare453 (p : Pattern) (guard : d1 p = 1) : d111 p ≤ (1 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d111, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare446 p hg
    simpa only [d111, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d111, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare452 p hg
    simpa only [d111, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare454 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (1 : Int) + d9 p := by
  change (10 : Int) ≤ (1 : Int) + 9
  decide
theorem compare455 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (1 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare454 p hg
    simpa only [d57, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d57, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare456 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (1 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare454 p hg
    simpa only [d58, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare455 p hg
    simpa only [d58, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare457 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (1 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare456 p hg
    simpa only [d59, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d59, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare458 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (1 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare456 p hg
    simpa only [d60, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare457 p hg
    simpa only [d60, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare459 (p : Pattern) (guard : d1 p = 1) : d112 p ≤ (1 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d112, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare458 p hg
    simpa only [d112, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d112, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d112, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare460 (p : Pattern) (guard : d1 p = 1) : d113 p ≤ (1 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d113, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare452 p hg
    simpa only [d113, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d113, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare459 p hg
    simpa only [d113, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare461 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (1 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d114, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare453 p hg
    simpa only [d114, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d114, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare460 p hg
    simpa only [d114, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare462 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (1 : Int) + d2 p := by
  change (3 : Int) ≤ (1 : Int) + 2
  decide
theorem compare463 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (1 : Int) + d30 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare462 p hg
    simpa only [d115, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d115, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare464 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (1 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare462 p hg
    simpa only [d116, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare463 p hg
    simpa only [d116, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare465 (p : Pattern) (guard : d1 p = 1) : d117 p ≤ (1 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d117, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare464 p hg
    simpa only [d117, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d117, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d117, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare466 (p : Pattern) (guard : d1 p = 1) : d118 p ≤ (1 : Int) + d33 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d118, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare444 p hg
    simpa only [d118, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d118, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare465 p hg
    simpa only [d118, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare467 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (1 : Int) + d6 p := by
  change (7 : Int) ≤ (1 : Int) + 6
  decide
theorem compare468 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (1 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare467 p hg
    simpa only [d119, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d119, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare469 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (1 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare467 p hg
    simpa only [d120, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare468 p hg
    simpa only [d120, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare470 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (1 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare469 p hg
    simpa only [d121, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d121, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare471 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (1 : Int) + d37 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare444 p hg
    simpa only [d122, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare470 p hg
    simpa only [d122, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare472 (p : Pattern) (guard : d1 p = 1) : d123 p ≤ (1 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d123, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare466 p hg
    simpa only [d123, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d123, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare471 p hg
    simpa only [d123, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare473 (p : Pattern) (guard : d1 p = 1) : d124 p ≤ (1 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d124, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare444 p hg
    simpa only [d124, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d124, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare419 p hg
    simpa only [d124, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare474 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (1 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare449 p hg
    simpa only [d125, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d125, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare475 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (1 : Int) + d44 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare473 p hg
    simpa only [d126, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare474 p hg
    simpa only [d126, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare476 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (1 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare472 p hg
    simpa only [d127, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare475 p hg
    simpa only [d127, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare477 (p : Pattern) (guard : d1 p = 1) : d124 p ≤ (1 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d124, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare444 p hg
    simpa only [d124, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d124, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d124, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare478 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (1 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare477 p hg
    simpa only [d126, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare474 p hg
    simpa only [d126, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare479 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (1 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare456 p hg
    simpa only [d70, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d70, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare480 (p : Pattern) (guard : d1 p = 1) : d128 p ≤ (1 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d128, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare479 p hg
    simpa only [d128, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d128, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d128, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare481 (p : Pattern) (guard : d1 p = 1) : d129 p ≤ (1 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d129, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare478 p hg
    simpa only [d129, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d129, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare480 p hg
    simpa only [d129, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare482 (p : Pattern) (guard : d1 p = 1) : d130 p ≤ (1 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d130, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare476 p hg
    simpa only [d130, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d130, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare481 p hg
    simpa only [d130, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare483 (p : Pattern) (guard : d1 p = 1) : d131 p ≤ (1 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d131, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare461 p hg
    simpa only [d131, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d131, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare482 p hg
    simpa only [d131, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare484 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (1 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare464 p hg
    simpa only [d132, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare465 p hg
    simpa only [d132, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare485 (p : Pattern) (guard : d1 p = 1) : d133 p ≤ (1 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d133, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare446 p hg
    simpa only [d133, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d133, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare484 p hg
    simpa only [d133, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare486 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (1 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d134, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare451 p hg
    simpa only [d134, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d134, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare458 p hg
    simpa only [d134, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare487 (p : Pattern) (guard : d1 p = 1) : d135 p ≤ (1 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d135, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare485 p hg
    simpa only [d135, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d135, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare486 p hg
    simpa only [d135, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare488 (p : Pattern) (guard : d1 p = 1) : d136 p ≤ (1 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d136, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare451 p hg
    simpa only [d136, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d136, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare401 p hg
    simpa only [d136, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare489 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare420 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare490 (p : Pattern) (guard : d1 p = 1) : d137 p ≤ (1 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d137, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare488 p hg
    simpa only [d137, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d137, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare489 p hg
    simpa only [d137, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare491 (p : Pattern) (guard : d1 p = 1) : d138 p ≤ (1 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d138, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare487 p hg
    simpa only [d138, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d138, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare490 p hg
    simpa only [d138, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare492 (p : Pattern) (guard : d1 p = 1) : d139 p ≤ (1 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d139, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare464 p hg
    simpa only [d139, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d139, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d139, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare493 (p : Pattern) (guard : d1 p = 1) : d140 p ≤ (1 : Int) + d67 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d140, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare471 p hg
    simpa only [d140, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d140, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare492 p hg
    simpa only [d140, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare494 (p : Pattern) (guard : d1 p = 1) : d141 p ≤ (1 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d141, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare474 p hg
    simpa only [d141, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d141, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare479 p hg
    simpa only [d141, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare495 (p : Pattern) (guard : d1 p = 1) : d142 p ≤ (1 : Int) + d69 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d142, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare493 p hg
    simpa only [d142, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d142, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare494 p hg
    simpa only [d142, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare496 (p : Pattern) (guard : d1 p = 1) : d143 p ≤ (1 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d143, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare474 p hg
    simpa only [d143, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d143, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare373 p hg
    simpa only [d143, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare497 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare388 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare498 (p : Pattern) (guard : d1 p = 1) : d144 p ≤ (1 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d144, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare496 p hg
    simpa only [d144, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d144, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare497 p hg
    simpa only [d144, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare499 (p : Pattern) (guard : d1 p = 1) : d145 p ≤ (1 : Int) + d75 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d145, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare495 p hg
    simpa only [d145, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d145, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare498 p hg
    simpa only [d145, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare500 (p : Pattern) (guard : d1 p = 1) : d146 p ≤ (1 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d146, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare491 p hg
    simpa only [d146, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d146, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare499 p hg
    simpa only [d146, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare501 (p : Pattern) (guard : d1 p = 1) : d147 p ≤ (1 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d147, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare483 p hg
    simpa only [d147, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d147, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d147, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare502 (p : Pattern) (guard : d1 p = 1) : d148 p ≤ (1 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d148, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare469 p hg
    simpa only [d148, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d148, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare470 p hg
    simpa only [d148, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare503 (p : Pattern) (guard : d1 p = 1) : d149 p ≤ (1 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d149, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare484 p hg
    simpa only [d149, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d149, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare502 p hg
    simpa only [d149, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare504 (p : Pattern) (guard : d1 p = 1) : d150 p ≤ (1 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d150, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare503 p hg
    simpa only [d150, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d150, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare489 p hg
    simpa only [d150, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare505 (p : Pattern) (guard : d1 p = 1) : d151 p ≤ (1 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d151, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare504 p hg
    simpa only [d151, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d151, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d151, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare506 (p : Pattern) (guard : d1 p = 1) : d152 p ≤ (1 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d152, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare461 p hg
    simpa only [d152, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d152, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare505 p hg
    simpa only [d152, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare507 (p : Pattern) (guard : d1 p = 1) : d153 p ≤ (1 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d153, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare502 p hg
    simpa only [d153, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d153, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d153, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare508 (p : Pattern) (guard : d1 p = 1) : d154 p ≤ (1 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d154, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare507 p hg
    simpa only [d154, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d154, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d154, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare509 (p : Pattern) (guard : d1 p = 1) : d155 p ≤ (1 : Int) + d85 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d155, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare508 p hg
    simpa only [d155, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d155, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d155, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare510 (p : Pattern) (guard : d1 p = 1) : d156 p ≤ (1 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d156, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare491 p hg
    simpa only [d156, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d156, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare509 p hg
    simpa only [d156, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare511 (p : Pattern) (guard : d1 p = 1) : d157 p ≤ (1 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d157, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare506 p hg
    simpa only [d157, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d157, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare510 p hg
    simpa only [d157, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare512 (p : Pattern) (guard : d1 p = 1) : d158 p ≤ (1 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d158, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare501 p hg
    simpa only [d158, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d158, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d158, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare513 (p : Pattern) (guard : d1 p = 1) : d112 p ≤ (1 : Int) + d89 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d112, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare458 p hg
    simpa only [d112, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d112, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare420 p hg
    simpa only [d112, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare514 (p : Pattern) (guard : d1 p = 1) : d159 p ≤ (1 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d159, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare513 p hg
    simpa only [d159, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d159, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare489 p hg
    simpa only [d159, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare515 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare489 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare516 (p : Pattern) (guard : d1 p = 1) : d160 p ≤ (1 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d160, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare514 p hg
    simpa only [d160, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d160, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare515 p hg
    simpa only [d160, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare517 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare515 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare518 (p : Pattern) (guard : d1 p = 1) : d161 p ≤ (1 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d161, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare516 p hg
    simpa only [d161, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d161, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare517 p hg
    simpa only [d161, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare519 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d95 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare517 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare520 (p : Pattern) (guard : d1 p = 1) : d162 p ≤ (1 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d162, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare518 p hg
    simpa only [d162, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d162, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare519 p hg
    simpa only [d162, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare521 (p : Pattern) (guard : d1 p = 1) : d163 p ≤ (1 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d163, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d163, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d163, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare520 p hg
    simpa only [d163, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare522 (p : Pattern) (guard : d1 p = 1) : d164 p ≤ (1 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d164, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare512 p hg
    simpa only [d164, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d164, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare521 p hg
    simpa only [d164, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare523 (p : Pattern) (guard : d1 p = 1) : d165 p ≤ (1 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d165, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d165, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d165, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d165, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare524 (p : Pattern) (guard : d1 p = 1) : d166 p ≤ (1 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d166, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare512 p hg
    simpa only [d166, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d166, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare523 p hg
    simpa only [d166, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare525 (p : Pattern) (guard : d1 p = 1) : d167 p ≤ (1 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d167, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare522 p hg
    simpa only [d167, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d167, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare524 p hg
    simpa only [d167, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare526 (p : Pattern) (guard : d1 p = 1) : d168 p ≤ (1 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare525 p hg
    simpa only [d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare527 (p : Pattern) (guard : d4039 p = 1) : d169 p ≤ (1 : Int) + d101 p := by
  cases selected : p 49 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4039, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare441 p hg
    simpa only [d4039, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4039, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare526 p hg
    simpa only [d4039, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare528 (p : Pattern) (guard : d0 p = 1) : d480 p ≤ (1 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare529 (p : Pattern) (guard : d4046 p = 1) : d481 p ≤ (1 : Int) + d101 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4039 p = 1 := by simpa only [d4046, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare527 p hg
    simpa only [d4046, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4046, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare528 p hg
    simpa only [d4046, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare530 (p : Pattern) (guard : d1 p = 1) : d169 p ≤ (1 : Int) + d169 p := by
  omega
theorem compare531 (p : Pattern) (guard : d0 p = 1) : d480 p ≤ (1 : Int) + d266 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare532 (p : Pattern) (guard : d4038 p = 1) : d481 p ≤ (1 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4038, d481, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare530 p hg
    simpa only [d4038, d481, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4038, d481, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare531 p hg
    simpa only [d4038, d481, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare533 (p : Pattern) (guard : d0 p = 1) : d480 p ≤ (0 : Int) + d311 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare534 (p : Pattern) (guard : d4044 p = 1) : d481 p ≤ (0 : Int) + d312 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4040 p = 1 := by simpa only [d4044, d481, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d4044, d481, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4044, d481, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare533 p hg
    simpa only [d4044, d481, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare535 (p : Pattern) (guard : d0 p = 1) : d101 p ≤ (0 : Int) + d446 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare536 (p : Pattern) (guard : d4042 p = 1) : d101 p ≤ (0 : Int) + d485 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare535 p hg
    simpa only [d4042, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare537 (p : Pattern) (guard : d0 p = 1) : d167 p ≤ (0 : Int) + d446 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare538 (p : Pattern) (guard : d4042 p = 1) : d168 p ≤ (0 : Int) + d485 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d168, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d168, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d168, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare537 p hg
    simpa only [d4042, d168, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare539 (p : Pattern) (guard : d4042 p = 1) : d169 p ≤ (0 : Int) + d485 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare538 p hg
    simpa only [d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare540 (p : Pattern) (guard : d0 p = 1) : d480 p ≤ (0 : Int) + d487 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare541 (p : Pattern) (guard : d4047 p = 1) : d481 p ≤ (0 : Int) + d488 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d4047, d481, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare539 p hg
    simpa only [d4047, d481, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4047, d481, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare540 p hg
    simpa only [d4047, d481, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare542 (p : Pattern) (guard : d0 p = 1) : d447 p ≤ (0 : Int) + d168 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare543 (p : Pattern) (guard : d4040 p = 1) : d482 p ≤ (0 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4040, d482, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4040, d482, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4040, d482, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare542 p hg
    simpa only [d4040, d482, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare544 (p : Pattern) (guard : d0 p = 1) : d479 p ≤ (0 : Int) + d310 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare545 (p : Pattern) (guard : d4040 p = 1) : d483 p ≤ (0 : Int) + d311 p := by
  cases selected : p 49 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4040, d483, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4040, d483, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4040, d483, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare544 p hg
    simpa only [d4040, d483, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare546 (p : Pattern) (guard : d4040 p = 1) : d484 p ≤ (0 : Int) + d312 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4040 p = 1 := by simpa only [d484, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare543 p hg
    simpa only [d484, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4040 p = 1 := by simpa only [d484, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare545 p hg
    simpa only [d484, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare547 (p : Pattern) (guard : d0 p = 1) : d447 p ≤ (0 : Int) + d485 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare548 (p : Pattern) (guard : d4048 p = 1) : d482 p ≤ (0 : Int) + d485 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d4048, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d4048, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4048, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare547 p hg
    simpa only [d4048, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare549 (p : Pattern) (guard : d0 p = 1) : d479 p ≤ (0 : Int) + d486 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare550 (p : Pattern) (guard : d4048 p = 1) : d483 p ≤ (0 : Int) + d487 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d4048, d483, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d4048, d483, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4048, d483, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare549 p hg
    simpa only [d4048, d483, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare551 (p : Pattern) (guard : d4048 p = 1) : d484 p ≤ (0 : Int) + d488 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4048 p = 1 := by simpa only [d484, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare548 p hg
    simpa only [d484, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4048 p = 1 := by simpa only [d484, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare550 p hg
    simpa only [d484, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare552 (p : Pattern) (guard : d4041 p = 1) : d101 p ≤ (0 : Int) + d101 p := by
  omega
theorem compare553 (p : Pattern) (guard : d0 p = 1) : d447 p ≤ (0 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare554 (p : Pattern) (guard : d4049 p = 1) : d482 p ≤ (0 : Int) + d101 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4041 p = 1 := by simpa only [d4049, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare552 p hg
    simpa only [d4049, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4049, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare553 p hg
    simpa only [d4049, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare555 (p : Pattern) (guard : d0 p = 1) : d479 p ≤ (0 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare556 (p : Pattern) (guard : d4049 p = 1) : d483 p ≤ (0 : Int) + d101 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4041 p = 1 := by simpa only [d4049, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare552 p hg
    simpa only [d4049, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4049, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare555 p hg
    simpa only [d4049, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare557 (p : Pattern) (guard : d4049 p = 1) : d484 p ≤ (0 : Int) + d101 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4049 p = 1 := by simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare554 p hg
    simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4049 p = 1 := by simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare556 p hg
    simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare558 (p : Pattern) (guard : d0 p = 1) : d447 p ≤ (1 : Int) + d168 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare559 (p : Pattern) (guard : d4040 p = 1) : d482 p ≤ (1 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4040, d482, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d4040, d482, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4040, d482, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare558 p hg
    simpa only [d4040, d482, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
