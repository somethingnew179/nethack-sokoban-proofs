/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons044
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6300 (p : Pattern) (guard : d4117 p = 1) : d725 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d725, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6297 p hg
    simpa only [d725, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d725, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6299 p hg
    simpa only [d725, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6301 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d81 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6302 (p : Pattern) (guard : d4117 p = 1) : d726 p ≤ (2 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d726, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5449 p hg
    simpa only [d4117, d726, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d726, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6301 p hg
    simpa only [d4117, d726, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6303 (p : Pattern) (guard : d4117 p = 1) : d727 p ≤ (2 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d727, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6302 p hg
    simpa only [d727, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d727, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6283 p hg
    simpa only [d727, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6304 (p : Pattern) (guard : d4117 p = 1) : d728 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d728, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6300 p hg
    simpa only [d728, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d728, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6303 p hg
    simpa only [d728, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6305 (p : Pattern) (guard : d4117 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare6306 (p : Pattern) (guard : d4117 p = 1) : d729 p ≤ (2 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d729, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6303 p hg
    simpa only [d729, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d729, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6305 p hg
    simpa only [d729, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6307 (p : Pattern) (guard : d4117 p = 1) : d730 p ≤ (2 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d730, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6304 p hg
    simpa only [d730, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d730, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6306 p hg
    simpa only [d730, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6308 (p : Pattern) (guard : d4117 p = 1) : d731 p ≤ (2 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d731, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6295 p hg
    simpa only [d731, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d731, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6307 p hg
    simpa only [d731, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6309 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (2 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6310 (p : Pattern) (guard : d4117 p = 1) : d732 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d732, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5449 p hg
    simpa only [d4117, d732, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d732, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6309 p hg
    simpa only [d4117, d732, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6311 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (2 : Int) + d75 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6312 (p : Pattern) (guard : d4117 p = 1) : d733 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d733, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5452 p hg
    simpa only [d4117, d733, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d733, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6311 p hg
    simpa only [d4117, d733, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6313 (p : Pattern) (guard : d4117 p = 1) : d734 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d734, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6310 p hg
    simpa only [d734, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d734, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6312 p hg
    simpa only [d734, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6314 (p : Pattern) (guard : d4117 p = 1) : d735 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d735, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6313 p hg
    simpa only [d735, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d735, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6303 p hg
    simpa only [d735, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6315 (p : Pattern) (guard : d4117 p = 1) : d736 p ≤ (2 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d736, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6284 p hg
    simpa only [d736, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d736, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6293 p hg
    simpa only [d736, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6316 (p : Pattern) (guard : d4117 p = 1) : d737 p ≤ (2 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d737, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6314 p hg
    simpa only [d737, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d737, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6315 p hg
    simpa only [d737, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6317 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (2 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6318 (p : Pattern) (guard : d4117 p = 1) : d717 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d717, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5449 p hg
    simpa only [d4117, d717, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d717, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6317 p hg
    simpa only [d4117, d717, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6319 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d75 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6320 (p : Pattern) (guard : d4117 p = 1) : d714 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5452 p hg
    simpa only [d4117, d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6319 p hg
    simpa only [d4117, d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6321 (p : Pattern) (guard : d4117 p = 1) : d718 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d718, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6318 p hg
    simpa only [d718, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d718, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6320 p hg
    simpa only [d718, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6322 (p : Pattern) (guard : d4117 p = 1) : d738 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d738, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6321 p hg
    simpa only [d738, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d738, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6303 p hg
    simpa only [d738, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6323 (p : Pattern) (guard : d4117 p = 1) : d739 p ≤ (2 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d739, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6322 p hg
    simpa only [d739, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d739, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6306 p hg
    simpa only [d739, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6324 (p : Pattern) (guard : d4117 p = 1) : d740 p ≤ (2 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d740, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6316 p hg
    simpa only [d740, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d740, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6323 p hg
    simpa only [d740, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6325 (p : Pattern) (guard : d4117 p = 1) : d741 p ≤ (2 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6308 p hg
    simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6324 p hg
    simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6326 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (2 : Int) + d130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6327 (p : Pattern) (guard : d4117 p = 1) : d742 p ≤ (2 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2155 p hg
    simpa only [d4117, d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6326 p hg
    simpa only [d4117, d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6328 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (2 : Int) + d145 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6329 (p : Pattern) (guard : d4117 p = 1) : d743 p ≤ (2 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d743, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5479 p hg
    simpa only [d4117, d743, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d743, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6328 p hg
    simpa only [d4117, d743, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6330 (p : Pattern) (guard : d4117 p = 1) : d744 p ≤ (2 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d744, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6327 p hg
    simpa only [d744, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d744, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6329 p hg
    simpa only [d744, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6331 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d151 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6332 (p : Pattern) (guard : d4117 p = 1) : d745 p ≤ (2 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d745, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2155 p hg
    simpa only [d4117, d745, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d745, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6331 p hg
    simpa only [d4117, d745, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6333 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6334 (p : Pattern) (guard : d4117 p = 1) : d746 p ≤ (2 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d746, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5479 p hg
    simpa only [d4117, d746, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d746, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6333 p hg
    simpa only [d4117, d746, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6335 (p : Pattern) (guard : d4117 p = 1) : d747 p ≤ (2 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d747, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6332 p hg
    simpa only [d747, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d747, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6334 p hg
    simpa only [d747, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6336 (p : Pattern) (guard : d4117 p = 1) : d748 p ≤ (2 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d748, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6330 p hg
    simpa only [d748, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d748, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6335 p hg
    simpa only [d748, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6337 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (2 : Int) + d151 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6338 (p : Pattern) (guard : d4117 p = 1) : d749 p ≤ (2 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d749, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2155 p hg
    simpa only [d4117, d749, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d749, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6337 p hg
    simpa only [d4117, d749, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6339 (p : Pattern) (guard : d4117 p = 1) : d750 p ≤ (2 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d750, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6338 p hg
    simpa only [d750, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d750, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6334 p hg
    simpa only [d750, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6340 (p : Pattern) (guard : d4117 p = 1) : d162 p ≤ (2 : Int) + d162 p := by
  omega
theorem compare6341 (p : Pattern) (guard : d4117 p = 1) : d751 p ≤ (2 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d751, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6339 p hg
    simpa only [d751, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d751, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6340 p hg
    simpa only [d751, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6342 (p : Pattern) (guard : d4117 p = 1) : d752 p ≤ (2 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d752, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6336 p hg
    simpa only [d752, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d752, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6341 p hg
    simpa only [d752, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6343 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (2 : Int) + d130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6344 (p : Pattern) (guard : d4117 p = 1) : d753 p ≤ (2 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d753, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2155 p hg
    simpa only [d4117, d753, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d753, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6343 p hg
    simpa only [d4117, d753, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6345 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d145 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6346 (p : Pattern) (guard : d4117 p = 1) : d746 p ≤ (2 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d746, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5479 p hg
    simpa only [d4117, d746, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d746, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6345 p hg
    simpa only [d4117, d746, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6347 (p : Pattern) (guard : d4117 p = 1) : d754 p ≤ (2 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d754, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6344 p hg
    simpa only [d754, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d754, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6346 p hg
    simpa only [d754, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6348 (p : Pattern) (guard : d4117 p = 1) : d755 p ≤ (2 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d755, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6347 p hg
    simpa only [d755, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d755, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6335 p hg
    simpa only [d755, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6349 (p : Pattern) (guard : d4117 p = 1) : d756 p ≤ (2 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d756, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6335 p hg
    simpa only [d756, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d756, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6305 p hg
    simpa only [d756, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6350 (p : Pattern) (guard : d4117 p = 1) : d757 p ≤ (2 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d757, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6348 p hg
    simpa only [d757, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d757, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6349 p hg
    simpa only [d757, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6351 (p : Pattern) (guard : d4117 p = 1) : d758 p ≤ (2 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d758, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6342 p hg
    simpa only [d758, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d758, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6350 p hg
    simpa only [d758, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6352 (p : Pattern) (guard : d4117 p = 1) : d759 p ≤ (2 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d759, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6308 p hg
    simpa only [d759, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d759, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6351 p hg
    simpa only [d759, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6353 (p : Pattern) (guard : d4117 p = 1) : d760 p ≤ (2 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d760, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6325 p hg
    simpa only [d760, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d760, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6352 p hg
    simpa only [d760, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6354 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (2 : Int) + d178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6355 (p : Pattern) (guard : d4117 p = 1) : d717 p ≤ (2 : Int) + d179 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d717, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5449 p hg
    simpa only [d4117, d717, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d717, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6354 p hg
    simpa only [d4117, d717, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6356 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d185 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6357 (p : Pattern) (guard : d4117 p = 1) : d714 p ≤ (2 : Int) + d186 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d714, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5452 p hg
    simpa only [d4117, d714, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d714, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6356 p hg
    simpa only [d4117, d714, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6358 (p : Pattern) (guard : d4117 p = 1) : d718 p ≤ (2 : Int) + d187 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d718, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6355 p hg
    simpa only [d718, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d718, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6357 p hg
    simpa only [d718, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6359 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d196 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6360 (p : Pattern) (guard : d4117 p = 1) : d761 p ≤ (2 : Int) + d197 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d761, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5494 p hg
    simpa only [d4117, d761, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d761, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6359 p hg
    simpa only [d4117, d761, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6361 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d203 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6362 (p : Pattern) (guard : d4117 p = 1) : d762 p ≤ (2 : Int) + d204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d762, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5497 p hg
    simpa only [d4117, d762, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d762, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6361 p hg
    simpa only [d4117, d762, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6363 (p : Pattern) (guard : d4117 p = 1) : d763 p ≤ (2 : Int) + d205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d763, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d763, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d763, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6362 p hg
    simpa only [d763, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6364 (p : Pattern) (guard : d4117 p = 1) : d764 p ≤ (2 : Int) + d206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d764, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6358 p hg
    simpa only [d764, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d764, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6363 p hg
    simpa only [d764, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6365 (p : Pattern) (guard : d4117 p = 1) : d765 p ≤ (2 : Int) + d207 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d765, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6363 p hg
    simpa only [d765, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d765, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6305 p hg
    simpa only [d765, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6366 (p : Pattern) (guard : d4117 p = 1) : d766 p ≤ (2 : Int) + d208 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d766, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6364 p hg
    simpa only [d766, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d766, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6365 p hg
    simpa only [d766, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6367 (p : Pattern) (guard : d4117 p = 1) : d767 p ≤ (2 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d767, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6316 p hg
    simpa only [d767, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d767, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6366 p hg
    simpa only [d767, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6368 (p : Pattern) (guard : d4117 p = 1) : d768 p ≤ (2 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d768, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6308 p hg
    simpa only [d768, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d768, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6367 p hg
    simpa only [d768, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6369 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (2 : Int) + d218 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6370 (p : Pattern) (guard : d4117 p = 1) : d769 p ≤ (2 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d769, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2185 p hg
    simpa only [d4117, d769, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d769, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6369 p hg
    simpa only [d4117, d769, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6371 (p : Pattern) (guard : d4117 p = 1) : d770 p ≤ (2 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d770, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6327 p hg
    simpa only [d770, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d770, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6370 p hg
    simpa only [d770, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6372 (p : Pattern) (guard : d4117 p = 1) : d771 p ≤ (2 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d771, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2185 p hg
    simpa only [d4117, d771, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d771, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6333 p hg
    simpa only [d4117, d771, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6373 (p : Pattern) (guard : d4117 p = 1) : d772 p ≤ (2 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d772, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6332 p hg
    simpa only [d772, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d772, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6372 p hg
    simpa only [d772, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6374 (p : Pattern) (guard : d4117 p = 1) : d773 p ≤ (2 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d773, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6371 p hg
    simpa only [d773, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d773, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6373 p hg
    simpa only [d773, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6375 (p : Pattern) (guard : d4117 p = 1) : d774 p ≤ (2 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d774, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6338 p hg
    simpa only [d774, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d774, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6372 p hg
    simpa only [d774, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6376 (p : Pattern) (guard : d4117 p = 1) : d775 p ≤ (2 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d775, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6375 p hg
    simpa only [d775, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d775, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6340 p hg
    simpa only [d775, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6377 (p : Pattern) (guard : d4117 p = 1) : d776 p ≤ (2 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d776, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6374 p hg
    simpa only [d776, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d776, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6376 p hg
    simpa only [d776, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6378 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (2 : Int) + d232 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6379 (p : Pattern) (guard : d4117 p = 1) : d753 p ≤ (2 : Int) + d233 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d753, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2155 p hg
    simpa only [d4117, d753, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d753, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6378 p hg
    simpa only [d4117, d753, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6380 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d238 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6381 (p : Pattern) (guard : d4117 p = 1) : d771 p ≤ (2 : Int) + d239 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d771, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2185 p hg
    simpa only [d4117, d771, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d771, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6380 p hg
    simpa only [d4117, d771, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6382 (p : Pattern) (guard : d4117 p = 1) : d777 p ≤ (2 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d777, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6379 p hg
    simpa only [d777, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d777, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6381 p hg
    simpa only [d777, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6383 (p : Pattern) (guard : d1 p = 1) : d243 p ≤ (2 : Int) + d243 p := by
  omega
theorem compare6384 (p : Pattern) (guard : d4117 p = 1) : d778 p ≤ (2 : Int) + d244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d778, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6383 p hg
    simpa only [d4117, d778, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d778, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6333 p hg
    simpa only [d4117, d778, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6385 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d248 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6386 (p : Pattern) (guard : d4117 p = 1) : d779 p ≤ (2 : Int) + d249 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d779, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5523 p hg
    simpa only [d4117, d779, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d779, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6385 p hg
    simpa only [d4117, d779, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6387 (p : Pattern) (guard : d4117 p = 1) : d780 p ≤ (2 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d780, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6384 p hg
    simpa only [d780, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d780, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6386 p hg
    simpa only [d780, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6388 (p : Pattern) (guard : d4117 p = 1) : d781 p ≤ (2 : Int) + d251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d781, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6382 p hg
    simpa only [d781, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d781, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6387 p hg
    simpa only [d781, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6389 (p : Pattern) (guard : d1 p = 1) : d256 p ≤ (2 : Int) + d256 p := by
  omega
theorem compare6390 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d259 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6391 (p : Pattern) (guard : d4117 p = 1) : d782 p ≤ (2 : Int) + d260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d782, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6389 p hg
    simpa only [d4117, d782, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d782, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6390 p hg
    simpa only [d4117, d782, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6392 (p : Pattern) (guard : d4117 p = 1) : d783 p ≤ (2 : Int) + d261 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d783, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6391 p hg
    simpa only [d783, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d783, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6386 p hg
    simpa only [d783, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6393 (p : Pattern) (guard : d4117 p = 1) : d784 p ≤ (2 : Int) + d262 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d784, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6392 p hg
    simpa only [d784, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d784, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6305 p hg
    simpa only [d784, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6394 (p : Pattern) (guard : d4117 p = 1) : d785 p ≤ (2 : Int) + d263 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d785, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6388 p hg
    simpa only [d785, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d785, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6393 p hg
    simpa only [d785, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6395 (p : Pattern) (guard : d4117 p = 1) : d786 p ≤ (2 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d786, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6377 p hg
    simpa only [d786, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d786, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6394 p hg
    simpa only [d786, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6396 (p : Pattern) (guard : d4117 p = 1) : d787 p ≤ (2 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d787, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6308 p hg
    simpa only [d787, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d787, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6395 p hg
    simpa only [d787, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6397 (p : Pattern) (guard : d4117 p = 1) : d788 p ≤ (2 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d788, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6368 p hg
    simpa only [d788, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d788, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6396 p hg
    simpa only [d788, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6398 (p : Pattern) (guard : d4117 p = 1) : d789 p ≤ (2 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d789, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6353 p hg
    simpa only [d789, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d789, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6397 p hg
    simpa only [d789, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6399 (p : Pattern) (guard : d4395 p = 1) : d22 p ≤ (0 : Int) + d949 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d22, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d22, d949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d22, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4213 p hg
    simpa only [d4395, d22, d949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6400 (p : Pattern) (guard : d0 p = 1) : d362 p ≤ (0 : Int) + d951 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6401 (p : Pattern) (guard : d4670 p = 1) : d790 p ≤ (0 : Int) + d952 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d790, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6399 p hg
    simpa only [d4670, d790, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d790, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6400 p hg
    simpa only [d4670, d790, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6402 (p : Pattern) (guard : d0 p = 1) : d79 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6403 (p : Pattern) (guard : d4395 p = 1) : d791 p ≤ (0 : Int) + d953 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d791, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4395, d791, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d791, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6402 p hg
    simpa only [d4395, d791, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6404 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d954 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6405 (p : Pattern) (guard : d4670 p = 1) : d792 p ≤ (0 : Int) + d955 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d792, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6403 p hg
    simpa only [d4670, d792, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d792, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6404 p hg
    simpa only [d4670, d792, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6406 (p : Pattern) (guard : d4670 p = 1) : d793 p ≤ (0 : Int) + d956 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d793, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6401 p hg
    simpa only [d793, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d793, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6405 p hg
    simpa only [d793, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6407 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (0 : Int) + d54 p := by
  omega
theorem compare6408 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d369 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6409 (p : Pattern) (guard : d4395 p = 1) : d56 p ≤ (0 : Int) + d957 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d56, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d56, d957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d56, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6408 p hg
    simpa only [d4395, d56, d957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6410 (p : Pattern) (guard : d0 p = 1) : d387 p ≤ (0 : Int) + d958 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6411 (p : Pattern) (guard : d4670 p = 1) : d794 p ≤ (0 : Int) + d959 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d794, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6409 p hg
    simpa only [d4670, d794, d959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d794, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6410 p hg
    simpa only [d4670, d794, d959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6412 (p : Pattern) (guard : d1 p = 1) : d796 p ≤ (0 : Int) + d796 p := by
  omega
theorem compare6413 (p : Pattern) (guard : d0 p = 1) : d798 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6414 (p : Pattern) (guard : d4395 p = 1) : d799 p ≤ (0 : Int) + d960 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d799, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d4395, d799, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d799, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6413 p hg
    simpa only [d4395, d799, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6415 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d961 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6416 (p : Pattern) (guard : d4670 p = 1) : d800 p ≤ (0 : Int) + d962 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d800, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6414 p hg
    simpa only [d4670, d800, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d800, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6415 p hg
    simpa only [d4670, d800, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6417 (p : Pattern) (guard : d4670 p = 1) : d801 p ≤ (0 : Int) + d963 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d801, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6411 p hg
    simpa only [d801, d963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d801, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6416 p hg
    simpa only [d801, d963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6418 (p : Pattern) (guard : d4670 p = 1) : d802 p ≤ (0 : Int) + d964 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d802, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d802, d964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d802, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6417 p hg
    simpa only [d802, d964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6419 (p : Pattern) (guard : d4395 p = 1) : d22 p ≤ (0 : Int) + d965 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d22, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d22, d965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d22, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4227 p hg
    simpa only [d4395, d22, d965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6420 (p : Pattern) (guard : d0 p = 1) : d394 p ≤ (0 : Int) + d966 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6421 (p : Pattern) (guard : d4670 p = 1) : d803 p ≤ (0 : Int) + d967 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d803, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6419 p hg
    simpa only [d4670, d803, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d803, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6420 p hg
    simpa only [d4670, d803, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6422 (p : Pattern) (guard : d0 p = 1) : d79 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6423 (p : Pattern) (guard : d4395 p = 1) : d804 p ≤ (0 : Int) + d968 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d804, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d804, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d804, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6422 p hg
    simpa only [d4395, d804, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6424 (p : Pattern) (guard : d4670 p = 1) : d805 p ≤ (0 : Int) + d969 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d805, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6423 p hg
    simpa only [d4670, d805, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d805, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d805, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6425 (p : Pattern) (guard : d4670 p = 1) : d806 p ≤ (0 : Int) + d970 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d806, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6421 p hg
    simpa only [d806, d970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d806, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6424 p hg
    simpa only [d806, d970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6426 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6427 (p : Pattern) (guard : d4395 p = 1) : d56 p ≤ (0 : Int) + d971 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d56, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d56, d971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d56, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d4395, d56, d971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6428 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d972 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6429 (p : Pattern) (guard : d4670 p = 1) : d807 p ≤ (0 : Int) + d973 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d807, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6427 p hg
    simpa only [d4670, d807, d973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d807, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6428 p hg
    simpa only [d4670, d807, d973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6430 (p : Pattern) (guard : d1 p = 1) : d808 p ≤ (0 : Int) + d808 p := by
  omega
theorem compare6431 (p : Pattern) (guard : d0 p = 1) : d809 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6432 (p : Pattern) (guard : d4395 p = 1) : d810 p ≤ (0 : Int) + d972 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d810, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6430 p hg
    simpa only [d4395, d810, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d810, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6431 p hg
    simpa only [d4395, d810, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6433 (p : Pattern) (guard : d4670 p = 1) : d811 p ≤ (0 : Int) + d974 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d811, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6432 p hg
    simpa only [d4670, d811, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d811, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d811, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6434 (p : Pattern) (guard : d4670 p = 1) : d812 p ≤ (0 : Int) + d975 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d812, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6429 p hg
    simpa only [d812, d975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d812, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6433 p hg
    simpa only [d812, d975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6435 (p : Pattern) (guard : d4670 p = 1) : d813 p ≤ (0 : Int) + d976 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d813, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6425 p hg
    simpa only [d813, d976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d813, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6434 p hg
    simpa only [d813, d976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6436 (p : Pattern) (guard : d4670 p = 1) : d814 p ≤ (0 : Int) + d977 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d814, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6418 p hg
    simpa only [d814, d977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d814, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6435 p hg
    simpa only [d814, d977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6437 (p : Pattern) (guard : d4395 p = 1) : d22 p ≤ (0 : Int) + d978 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d22, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d22, d978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d22, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4240 p hg
    simpa only [d4395, d22, d978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6438 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (0 : Int) + d966 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6439 (p : Pattern) (guard : d4670 p = 1) : d815 p ≤ (0 : Int) + d979 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d815, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6437 p hg
    simpa only [d4670, d815, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d815, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6438 p hg
    simpa only [d4670, d815, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
