/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons259
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare36400 (p : Pattern) (guard : d8099 p = 1) : d3587 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36399 p hg
    simpa only [d8099, d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31561 p hg
    simpa only [d8099, d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36401 (p : Pattern) (guard : d8100 p = 1) : d3643 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36398 p hg
    simpa only [d8100, d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36400 p hg
    simpa only [d8100, d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36402 (p : Pattern) (guard : d8106 p = 1) : d3644 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36401 p hg
    simpa only [d8106, d3644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36403 (p : Pattern) (guard : d8107 p = 1) : d3645 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3645, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36396 p hg
    simpa only [d8107, d3645, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3645, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36402 p hg
    simpa only [d8107, d3645, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36404 (p : Pattern) (guard : d8099 p = 1) : d23 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36135 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36405 (p : Pattern) (guard : d0 p = 1) : d3567 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36406 (p : Pattern) (guard : d8105 p = 1) : d3568 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36404 p hg
    simpa only [d8105, d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36405 p hg
    simpa only [d8105, d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36407 (p : Pattern) (guard : d8111 p = 1) : d3611 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36406 p hg
    simpa only [d8111, d3611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36408 (p : Pattern) (guard : d8112 p = 1) : d3646 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36354 p hg
    simpa only [d8112, d3646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36407 p hg
    simpa only [d8112, d3646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36409 (p : Pattern) (guard : d8113 p = 1) : d3647 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3647, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36403 p hg
    simpa only [d8113, d3647, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3647, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36408 p hg
    simpa only [d8113, d3647, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36410 (p : Pattern) (guard : d8099 p = 1) : d57 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36143 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36411 (p : Pattern) (guard : d0 p = 1) : d3633 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36412 (p : Pattern) (guard : d8105 p = 1) : d3634 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36410 p hg
    simpa only [d8105, d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36411 p hg
    simpa only [d8105, d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36413 (p : Pattern) (guard : d8111 p = 1) : d3648 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36412 p hg
    simpa only [d8111, d3648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36414 (p : Pattern) (guard : d8112 p = 1) : d3649 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36354 p hg
    simpa only [d8112, d3649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36413 p hg
    simpa only [d8112, d3649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36415 (p : Pattern) (guard : d8099 p = 1) : d39 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36150 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36416 (p : Pattern) (guard : d0 p = 1) : d3598 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36417 (p : Pattern) (guard : d8105 p = 1) : d3638 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36415 p hg
    simpa only [d8105, d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36416 p hg
    simpa only [d8105, d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36418 (p : Pattern) (guard : d8111 p = 1) : d3650 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36417 p hg
    simpa only [d8111, d3650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36419 (p : Pattern) (guard : d8117 p = 1) : d3651 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36418 p hg
    simpa only [d8117, d3651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36420 (p : Pattern) (guard : d8118 p = 1) : d3652 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36414 p hg
    simpa only [d8118, d3652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36419 p hg
    simpa only [d8118, d3652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36421 (p : Pattern) (guard : d8119 p = 1) : d3653 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3653, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36409 p hg
    simpa only [d8119, d3653, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3653, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36420 p hg
    simpa only [d8119, d3653, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36422 (p : Pattern) (guard : d8120 p = 1) : d3713 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3713, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36392 p hg
    simpa only [d8120, d3713, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3713, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36421 p hg
    simpa only [d8120, d3713, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36423 (p : Pattern) (guard : d8121 p = 1) : d3714 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d3714, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36362 p hg
    simpa only [d8121, d3714, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d3714, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36422 p hg
    simpa only [d8121, d3714, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36424 (p : Pattern) (guard : d8089 p = 1) : d3656 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35890 p hg
    simpa only [d8089, d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36341 p hg
    simpa only [d8089, d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36425 (p : Pattern) (guard : d8090 p = 1) : d3657 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35993 p hg
    simpa only [d8090, d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36424 p hg
    simpa only [d8090, d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36426 (p : Pattern) (guard : d8091 p = 1) : d3658 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3658, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36120 p hg
    simpa only [d8091, d3658, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3658, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36425 p hg
    simpa only [d8091, d3658, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36427 (p : Pattern) (guard : d8095 p = 1) : d3659 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36306 p hg
    simpa only [d8095, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36428 (p : Pattern) (guard : d8096 p = 1) : d3660 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3660, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36426 p hg
    simpa only [d8096, d3660, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3660, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36427 p hg
    simpa only [d8096, d3660, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36429 (p : Pattern) (guard : d5854 p = 1) : d3662 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36304 p hg
    simpa only [d5854, d3662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29374 p hg
    simpa only [d5854, d3662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36430 (p : Pattern) (guard : d8094 p = 1) : d3663 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36342 p hg
    simpa only [d8094, d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36429 p hg
    simpa only [d8094, d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36431 (p : Pattern) (guard : d8100 p = 1) : d3664 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36430 p hg
    simpa only [d8100, d3664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36432 (p : Pattern) (guard : d8101 p = 1) : d3665 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3665, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36395 p hg
    simpa only [d8101, d3665, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3665, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36431 p hg
    simpa only [d8101, d3665, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36433 (p : Pattern) (guard : d8102 p = 1) : d3666 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3666, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36428 p hg
    simpa only [d8102, d3666, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3666, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36432 p hg
    simpa only [d8102, d3666, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36434 (p : Pattern) (guard : d8100 p = 1) : d3667 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36344 p hg
    simpa only [d8100, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36435 (p : Pattern) (guard : d8101 p = 1) : d3668 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36345 p hg
    simpa only [d8101, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36434 p hg
    simpa only [d8101, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36436 (p : Pattern) (guard : d8105 p = 1) : d3669 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36352 p hg
    simpa only [d8105, d3669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36437 (p : Pattern) (guard : d8106 p = 1) : d3670 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36353 p hg
    simpa only [d8106, d3670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36436 p hg
    simpa only [d8106, d3670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36438 (p : Pattern) (guard : d8107 p = 1) : d3671 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36435 p hg
    simpa only [d8107, d3671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36437 p hg
    simpa only [d8107, d3671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36439 (p : Pattern) (guard : d8108 p = 1) : d3672 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3672, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36433 p hg
    simpa only [d8108, d3672, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3672, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36438 p hg
    simpa only [d8108, d3672, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36440 (p : Pattern) (guard : d8112 p = 1) : d3675 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36233 p hg
    simpa only [d8112, d3675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36441 (p : Pattern) (guard : d8113 p = 1) : d3676 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36438 p hg
    simpa only [d8113, d3676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36440 p hg
    simpa only [d8113, d3676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36442 (p : Pattern) (guard : d8114 p = 1) : d3677 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3677, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36439 p hg
    simpa only [d8114, d3677, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3677, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36441 p hg
    simpa only [d8114, d3677, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36443 (p : Pattern) (guard : d8090 p = 1) : d30 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36057 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36126 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36444 (p : Pattern) (guard : d8095 p = 1) : d3643 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36443 p hg
    simpa only [d8095, d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36131 p hg
    simpa only [d8095, d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36445 (p : Pattern) (guard : d8101 p = 1) : d3678 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36444 p hg
    simpa only [d8101, d3678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36224 p hg
    simpa only [d8101, d3678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36446 (p : Pattern) (guard : d5854 p = 1) : d34 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36197 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36447 (p : Pattern) (guard : d8094 p = 1) : d34 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36198 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36446 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36448 (p : Pattern) (guard : d5854 p = 1) : d3590 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36197 p hg
    simpa only [d5854, d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17131 p hg
    simpa only [d5854, d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36449 (p : Pattern) (guard : d8099 p = 1) : d3593 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36448 p hg
    simpa only [d8099, d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31567 p hg
    simpa only [d8099, d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36450 (p : Pattern) (guard : d8100 p = 1) : d3679 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36447 p hg
    simpa only [d8100, d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36449 p hg
    simpa only [d8100, d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36451 (p : Pattern) (guard : d8105 p = 1) : d3594 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36449 p hg
    simpa only [d8105, d3594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36452 (p : Pattern) (guard : d8106 p = 1) : d3680 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36450 p hg
    simpa only [d8106, d3680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36451 p hg
    simpa only [d8106, d3680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36453 (p : Pattern) (guard : d8107 p = 1) : d3681 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36445 p hg
    simpa only [d8107, d3681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36452 p hg
    simpa only [d8107, d3681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36454 (p : Pattern) (guard : d8113 p = 1) : d3682 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36453 p hg
    simpa only [d8113, d3682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36241 p hg
    simpa only [d8113, d3682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36455 (p : Pattern) (guard : d8119 p = 1) : d3683 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36454 p hg
    simpa only [d8119, d3683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d3683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36456 (p : Pattern) (guard : d8120 p = 1) : d3684 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3684, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36442 p hg
    simpa only [d8120, d3684, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3684, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36455 p hg
    simpa only [d8120, d3684, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36457 (p : Pattern) (guard : d8085 p = 1) : d13 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35886 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36458 (p : Pattern) (guard : d8090 p = 1) : d13 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36457 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36339 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36459 (p : Pattern) (guard : d8095 p = 1) : d3582 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36458 p hg
    simpa only [d8095, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36344 p hg
    simpa only [d8095, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36460 (p : Pattern) (guard : d8101 p = 1) : d3665 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3665, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36459 p hg
    simpa only [d8101, d3665, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3665, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36431 p hg
    simpa only [d8101, d3665, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36461 (p : Pattern) (guard : d8105 p = 1) : d3588 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36400 p hg
    simpa only [d8105, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36462 (p : Pattern) (guard : d8106 p = 1) : d3678 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36401 p hg
    simpa only [d8106, d3678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36461 p hg
    simpa only [d8106, d3678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36463 (p : Pattern) (guard : d8107 p = 1) : d3685 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3685, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36460 p hg
    simpa only [d8107, d3685, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3685, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36462 p hg
    simpa only [d8107, d3685, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36464 (p : Pattern) (guard : d0 p = 1) : d3673 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36465 (p : Pattern) (guard : d8111 p = 1) : d3674 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36406 p hg
    simpa only [d8111, d3674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36464 p hg
    simpa only [d8111, d3674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36466 (p : Pattern) (guard : d8112 p = 1) : d3686 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36437 p hg
    simpa only [d8112, d3686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36465 p hg
    simpa only [d8112, d3686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36467 (p : Pattern) (guard : d8113 p = 1) : d3687 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3687, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36463 p hg
    simpa only [d8113, d3687, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3687, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36466 p hg
    simpa only [d8113, d3687, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36468 (p : Pattern) (guard : d0 p = 1) : d3635 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36469 (p : Pattern) (guard : d8111 p = 1) : d3636 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36412 p hg
    simpa only [d8111, d3636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36468 p hg
    simpa only [d8111, d3636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36470 (p : Pattern) (guard : d8112 p = 1) : d3688 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36437 p hg
    simpa only [d8112, d3688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36469 p hg
    simpa only [d8112, d3688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36471 (p : Pattern) (guard : d0 p = 1) : d3599 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36472 (p : Pattern) (guard : d8111 p = 1) : d3639 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36417 p hg
    simpa only [d8111, d3639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36471 p hg
    simpa only [d8111, d3639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36473 (p : Pattern) (guard : d8117 p = 1) : d3640 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36472 p hg
    simpa only [d8117, d3640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36474 (p : Pattern) (guard : d8118 p = 1) : d3689 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36470 p hg
    simpa only [d8118, d3689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36473 p hg
    simpa only [d8118, d3689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36475 (p : Pattern) (guard : d8119 p = 1) : d3690 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3690, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36467 p hg
    simpa only [d8119, d3690, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3690, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36474 p hg
    simpa only [d8119, d3690, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36476 (p : Pattern) (guard : d8112 p = 1) : d3691 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36452 p hg
    simpa only [d8112, d3691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36477 (p : Pattern) (guard : d8118 p = 1) : d3692 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36476 p hg
    simpa only [d8118, d3692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36478 (p : Pattern) (guard : d8124 p = 1) : d3693 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36477 p hg
    simpa only [d8124, d3693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36479 (p : Pattern) (guard : d8125 p = 1) : d3694 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3694, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36475 p hg
    simpa only [d8125, d3694, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3694, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36478 p hg
    simpa only [d8125, d3694, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36480 (p : Pattern) (guard : d8126 p = 1) : d3695 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3695, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36456 p hg
    simpa only [d8126, d3695, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3695, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36479 p hg
    simpa only [d8126, d3695, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36481 (p : Pattern) (guard : d8127 p = 1) : d3715 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d3715, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36423 p hg
    simpa only [d8127, d3715, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d3715, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36480 p hg
    simpa only [d8127, d3715, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36482 (p : Pattern) (guard : d8091 p = 1) : d3658 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3658, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36216 p hg
    simpa only [d8091, d3658, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3658, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36425 p hg
    simpa only [d8091, d3658, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36483 (p : Pattern) (guard : d8096 p = 1) : d3660 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3660, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36482 p hg
    simpa only [d8096, d3660, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3660, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36427 p hg
    simpa only [d8096, d3660, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36484 (p : Pattern) (guard : d8102 p = 1) : d3666 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3666, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36483 p hg
    simpa only [d8102, d3666, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3666, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36460 p hg
    simpa only [d8102, d3666, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36485 (p : Pattern) (guard : d8101 p = 1) : d3668 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3668, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36395 p hg
    simpa only [d8101, d3668, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3668, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36434 p hg
    simpa only [d8101, d3668, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36486 (p : Pattern) (guard : d8107 p = 1) : d3671 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3671, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36485 p hg
    simpa only [d8107, d3671, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3671, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36437 p hg
    simpa only [d8107, d3671, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36487 (p : Pattern) (guard : d8108 p = 1) : d3672 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3672, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36484 p hg
    simpa only [d8108, d3672, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3672, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36486 p hg
    simpa only [d8108, d3672, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36488 (p : Pattern) (guard : d8114 p = 1) : d3677 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3677, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36487 p hg
    simpa only [d8114, d3677, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3677, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36441 p hg
    simpa only [d8114, d3677, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36489 (p : Pattern) (guard : d8120 p = 1) : d3684 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3684, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36488 p hg
    simpa only [d8120, d3684, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3684, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36455 p hg
    simpa only [d8120, d3684, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36490 (p : Pattern) (guard : d8085 p = 1) : d13 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35987 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36491 (p : Pattern) (guard : d8090 p = 1) : d13 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36490 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36339 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36492 (p : Pattern) (guard : d8095 p = 1) : d3582 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36491 p hg
    simpa only [d8095, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36344 p hg
    simpa only [d8095, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36493 (p : Pattern) (guard : d8101 p = 1) : d3665 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3665, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36492 p hg
    simpa only [d8101, d3665, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3665, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36431 p hg
    simpa only [d8101, d3665, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36494 (p : Pattern) (guard : d8107 p = 1) : d3685 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3685, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36493 p hg
    simpa only [d8107, d3685, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3685, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36462 p hg
    simpa only [d8107, d3685, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36495 (p : Pattern) (guard : d8113 p = 1) : d3687 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3687, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36494 p hg
    simpa only [d8113, d3687, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3687, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36466 p hg
    simpa only [d8113, d3687, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36496 (p : Pattern) (guard : d8119 p = 1) : d3690 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3690, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36495 p hg
    simpa only [d8119, d3690, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3690, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36474 p hg
    simpa only [d8119, d3690, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36497 (p : Pattern) (guard : d8125 p = 1) : d3694 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3694, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36496 p hg
    simpa only [d8125, d3694, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3694, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36478 p hg
    simpa only [d8125, d3694, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36498 (p : Pattern) (guard : d8126 p = 1) : d3695 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3695, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36489 p hg
    simpa only [d8126, d3695, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3695, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36497 p hg
    simpa only [d8126, d3695, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36499 (p : Pattern) (guard : d8131 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare36500 (p : Pattern) (guard : d8132 p = 1) : d3716 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3716, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36498 p hg
    simpa only [d8132, d3716, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3716, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d8132, d3716, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36501 (p : Pattern) (guard : d8133 p = 1) : d3717 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d3717, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36481 p hg
    simpa only [d8133, d3717, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d3717, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36500 p hg
    simpa only [d8133, d3717, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36502 (p : Pattern) (guard : d8134 p = 1) : d3718 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d3718, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36302 p hg
    simpa only [d8134, d3718, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d3718, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36501 p hg
    simpa only [d8134, d3718, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36503 (p : Pattern) (guard : d1 p = 1) : d2051 p ≤ (0 : Int) + d428 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2051, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d2051, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2051, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14597 p hg
    simpa only [d2051, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36504 (p : Pattern) (guard : d1 p = 1) : d3719 p ≤ (0 : Int) + d429 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3719, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36503 p hg
    simpa only [d3719, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3719, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1519 p hg
    simpa only [d3719, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36505 (p : Pattern) (guard : d1 p = 1) : d3720 p ≤ (0 : Int) + d430 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3720, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36504 p hg
    simpa only [d3720, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3720, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35987 p hg
    simpa only [d3720, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36506 (p : Pattern) (guard : d1 p = 1) : d3721 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3721, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36505 p hg
    simpa only [d3721, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3721, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36119 p hg
    simpa only [d3721, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36507 (p : Pattern) (guard : d1 p = 1) : d3544 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3544, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35987 p hg
    simpa only [d3544, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3544, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35874 p hg
    simpa only [d3544, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36508 (p : Pattern) (guard : d8086 p = 1) : d3545 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3545, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36507 p hg
    simpa only [d8086, d3545, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3545, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35891 p hg
    simpa only [d8086, d3545, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36509 (p : Pattern) (guard : d8087 p = 1) : d3722 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d3722, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36506 p hg
    simpa only [d8087, d3722, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d3722, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36508 p hg
    simpa only [d8087, d3722, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36510 (p : Pattern) (guard : d1 p = 1) : d3548 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3548, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35869 p hg
    simpa only [d3548, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3548, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35878 p hg
    simpa only [d3548, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36511 (p : Pattern) (guard : d8086 p = 1) : d3549 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3549, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36510 p hg
    simpa only [d8086, d3549, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3549, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35896 p hg
    simpa only [d8086, d3549, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36512 (p : Pattern) (guard : d8091 p = 1) : d3550 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3550, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36511 p hg
    simpa only [d8091, d3550, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3550, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3550, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36513 (p : Pattern) (guard : d8092 p = 1) : d3723 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3723, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36509 p hg
    simpa only [d8092, d3723, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3723, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36512 p hg
    simpa only [d8092, d3723, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36514 (p : Pattern) (guard : d8086 p = 1) : d13 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35902 p hg
    simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36393 p hg
    simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36515 (p : Pattern) (guard : d8091 p = 1) : d3552 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3552, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36514 p hg
    simpa only [d8091, d3552, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3552, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36306 p hg
    simpa only [d8091, d3552, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36516 (p : Pattern) (guard : d8085 p = 1) : d3548 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3548, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35884 p hg
    simpa only [d8085, d3548, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3548, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35895 p hg
    simpa only [d8085, d3548, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36517 (p : Pattern) (guard : d8090 p = 1) : d3549 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3549, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36516 p hg
    simpa only [d8090, d3549, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3549, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36310 p hg
    simpa only [d8090, d3549, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36518 (p : Pattern) (guard : d8095 p = 1) : d3550 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3550, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36517 p hg
    simpa only [d8095, d3550, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3550, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3550, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36519 (p : Pattern) (guard : d8096 p = 1) : d3553 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3553, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36515 p hg
    simpa only [d8096, d3553, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3553, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36518 p hg
    simpa only [d8096, d3553, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36520 (p : Pattern) (guard : d8097 p = 1) : d3724 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d3724, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36513 p hg
    simpa only [d8097, d3724, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d3724, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36519 p hg
    simpa only [d8097, d3724, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36521 (p : Pattern) (guard : d8085 p = 1) : d17 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35942 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35914 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36522 (p : Pattern) (guard : d8090 p = 1) : d17 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36521 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36017 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36523 (p : Pattern) (guard : d8095 p = 1) : d3558 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3558, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36522 p hg
    simpa only [d8095, d3558, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3558, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36319 p hg
    simpa only [d8095, d3558, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36524 (p : Pattern) (guard : d8101 p = 1) : d3563 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3563, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36523 p hg
    simpa only [d8101, d3563, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3563, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36324 p hg
    simpa only [d8101, d3563, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36525 (p : Pattern) (guard : d8102 p = 1) : d3564 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3564, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36365 p hg
    simpa only [d8102, d3564, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3564, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36524 p hg
    simpa only [d8102, d3564, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36526 (p : Pattern) (guard : d8103 p = 1) : d3725 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3725, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36520 p hg
    simpa only [d8103, d3725, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3725, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36525 p hg
    simpa only [d8103, d3725, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36527 (p : Pattern) (guard : d8102 p = 1) : d3564 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3564, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36313 p hg
    simpa only [d8102, d3564, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3564, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36383 p hg
    simpa only [d8102, d3564, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36528 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36529 (p : Pattern) (guard : d8085 p = 1) : d23 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36528 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35951 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36530 (p : Pattern) (guard : d8090 p = 1) : d23 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36529 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36032 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36531 (p : Pattern) (guard : d8095 p = 1) : d3568 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3568, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36530 p hg
    simpa only [d8095, d3568, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3568, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36036 p hg
    simpa only [d8095, d3568, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36532 (p : Pattern) (guard : d8101 p = 1) : d3573 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3573, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36531 p hg
    simpa only [d8101, d3573, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3573, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36084 p hg
    simpa only [d8101, d3573, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36533 (p : Pattern) (guard : d8107 p = 1) : d3574 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3574, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36532 p hg
    simpa only [d8107, d3574, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3574, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d3574, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36534 (p : Pattern) (guard : d8108 p = 1) : d3575 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3575, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36527 p hg
    simpa only [d8108, d3575, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3575, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36533 p hg
    simpa only [d8108, d3575, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36535 (p : Pattern) (guard : d8109 p = 1) : d3726 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d3726, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36526 p hg
    simpa only [d8109, d3726, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d3726, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36534 p hg
    simpa only [d8109, d3726, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36536 (p : Pattern) (guard : d8096 p = 1) : d3589 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3589, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36217 p hg
    simpa only [d8096, d3589, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3589, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36193 p hg
    simpa only [d8096, d3589, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36537 (p : Pattern) (guard : d8101 p = 1) : d3595 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3595, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36459 p hg
    simpa only [d8101, d3595, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3595, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36205 p hg
    simpa only [d8101, d3595, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36538 (p : Pattern) (guard : d8102 p = 1) : d3596 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3596, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36536 p hg
    simpa only [d8102, d3596, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3596, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36537 p hg
    simpa only [d8102, d3596, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36539 (p : Pattern) (guard : d8101 p = 1) : d3600 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3600, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36395 p hg
    simpa only [d8101, d3600, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3600, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36114 p hg
    simpa only [d8101, d3600, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
