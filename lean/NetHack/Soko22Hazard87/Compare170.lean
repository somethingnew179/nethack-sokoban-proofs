import NetHack.Soko22Hazard87.Compare169
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare42500 (p : Pattern) (guard : d349139 p = 1) : d51038 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d349138 p = 1 := by simpa only [d349139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42499 p hg
    simpa only [d349139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42432 p hg
    simpa only [d349139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42501 (p : Pattern) (guard : d349140 p = 1) : d51038 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d349139 p = 1 := by simpa only [d349140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42500 p hg
    simpa only [d349140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42432 p hg
    simpa only [d349140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42502 (p : Pattern) (guard : d349141 p = 1) : d51038 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d349140 p = 1 := by simpa only [d349141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42501 p hg
    simpa only [d349141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42432 p hg
    simpa only [d349141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42503 (p : Pattern) (guard : d349142 p = 1) : d51039 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d349136 p = 1 := by simpa only [d349142, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42431 p hg
    simpa only [d349142, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349141 p = 1 := by simpa only [d349142, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42502 p hg
    simpa only [d349142, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42504 (p : Pattern) (guard : d0 p = 1) : d51079 p ≤ (0 : Int) + d47809 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42505 (p : Pattern) (guard : d0 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42506 (p : Pattern) (guard : d0 p = 1) : d51057 p ≤ (0 : Int) + d47786 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42507 (p : Pattern) (guard : d0 p = 1) : d51066 p ≤ (0 : Int) + d47796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42508 (p : Pattern) (guard : d0 p = 1) : d51073 p ≤ (0 : Int) + d47803 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42509 (p : Pattern) (guard : d0 p = 1) : d50874 p ≤ (0 : Int) + d47652 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42510 (p : Pattern) (guard : d0 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42511 (p : Pattern) (guard : d14 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare42512 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d47629 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42513 (p : Pattern) (guard : d15 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42511 p hg
    simpa only [d15, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42512 p hg
    simpa only [d15, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42514 (p : Pattern) (guard : d16 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42513 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42515 (p : Pattern) (guard : d17 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42514 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42516 (p : Pattern) (guard : d38813 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42515 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42517 (p : Pattern) (guard : d258091 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38813 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42516 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42518 (p : Pattern) (guard : d337158 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258091 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42517 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42519 (p : Pattern) (guard : d337173 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337158 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42518 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42520 (p : Pattern) (guard : d257183 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42516 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42521 (p : Pattern) (guard : d257184 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42520 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42522 (p : Pattern) (guard : d257185 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42521 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42523 (p : Pattern) (guard : d348400 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337173 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42519 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42522 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42524 (p : Pattern) (guard : d0 p = 1) : d50850 p ≤ (0 : Int) + d47631 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42525 (p : Pattern) (guard : d348401 p = 1) : d50874 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348400 p = 1 := by simpa only [d348401, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42523 p hg
    simpa only [d348401, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348401, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42524 p hg
    simpa only [d348401, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42526 (p : Pattern) (guard : d348402 p = 1) : d50874 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348401 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42525 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42509 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42527 (p : Pattern) (guard : d348547 p = 1) : d50874 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42509 p hg
    simpa only [d348547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348402 p = 1 := by simpa only [d348547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42526 p hg
    simpa only [d348547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42528 (p : Pattern) (guard : d348403 p = 1) : d51067 p ≤ (0 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348402 p = 1 := by simpa only [d348403, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42348 p hg
    simpa only [d348403, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348403, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42457 p hg
    simpa only [d348403, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42529 (p : Pattern) (guard : d348548 p = 1) : d51068 p ≤ (0 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348547 p = 1 := by simpa only [d348548, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42527 p hg
    simpa only [d348548, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348403 p = 1 := by simpa only [d348548, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42528 p hg
    simpa only [d348548, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42530 (p : Pattern) (guard : d0 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42531 (p : Pattern) (guard : d14 p = 1) : d6 p ≤ (0 : Int) + d6 p := by
  omega
theorem compare42532 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d47633 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42533 (p : Pattern) (guard : d15 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42531 p hg
    simpa only [d15, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42532 p hg
    simpa only [d15, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42534 (p : Pattern) (guard : d16 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42533 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42535 (p : Pattern) (guard : d17 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42534 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42536 (p : Pattern) (guard : d38813 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42535 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42537 (p : Pattern) (guard : d258091 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38813 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42536 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42538 (p : Pattern) (guard : d337158 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258091 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42537 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42539 (p : Pattern) (guard : d337173 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337158 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42538 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42540 (p : Pattern) (guard : d257183 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42536 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42541 (p : Pattern) (guard : d257184 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42540 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42542 (p : Pattern) (guard : d257185 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42541 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42543 (p : Pattern) (guard : d348400 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337173 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42539 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42542 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42544 (p : Pattern) (guard : d0 p = 1) : d50853 p ≤ (0 : Int) + d47635 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42545 (p : Pattern) (guard : d348401 p = 1) : d50900 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348400 p = 1 := by simpa only [d348401, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42543 p hg
    simpa only [d348401, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348401, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42544 p hg
    simpa only [d348401, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42546 (p : Pattern) (guard : d0 p = 1) : d50900 p ≤ (0 : Int) + d47677 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42547 (p : Pattern) (guard : d348402 p = 1) : d50900 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348401 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42545 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42546 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42548 (p : Pattern) (guard : d348403 p = 1) : d50908 p ≤ (0 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348402 p = 1 := by simpa only [d348403, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42547 p hg
    simpa only [d348403, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348403, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d348403, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42549 (p : Pattern) (guard : d348404 p = 1) : d50909 p ≤ (0 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348403 p = 1 := by simpa only [d348404, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42548 p hg
    simpa only [d348404, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348404, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d348404, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42550 (p : Pattern) (guard : d348549 p = 1) : d51069 p ≤ (0 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d348548 p = 1 := by simpa only [d348549, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42529 p hg
    simpa only [d348549, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348404 p = 1 := by simpa only [d348549, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42549 p hg
    simpa only [d348549, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42551 (p : Pattern) (guard : d0 p = 1) : d51072 p ≤ (0 : Int) + d47802 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42552 (p : Pattern) (guard : d348550 p = 1) : d51073 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d348549 p = 1 := by simpa only [d348550, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42550 p hg
    simpa only [d348550, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348550, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42551 p hg
    simpa only [d348550, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42553 (p : Pattern) (guard : d348551 p = 1) : d51073 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42508 p hg
    simpa only [d348551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348550 p = 1 := by simpa only [d348551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42552 p hg
    simpa only [d348551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42554 (p : Pattern) (guard : d348552 p = 1) : d51073 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42508 p hg
    simpa only [d348552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348551 p = 1 := by simpa only [d348552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42553 p hg
    simpa only [d348552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42555 (p : Pattern) (guard : d348556 p = 1) : d51073 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d348550 p = 1 := by simpa only [d348556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42552 p hg
    simpa only [d348556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42508 p hg
    simpa only [d348556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42556 (p : Pattern) (guard : d348562 p = 1) : d51073 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42508 p hg
    simpa only [d348562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348556 p = 1 := by simpa only [d348562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42555 p hg
    simpa only [d348562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42557 (p : Pattern) (guard : d348563 p = 1) : d51073 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348552 p = 1 := by simpa only [d348563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42554 p hg
    simpa only [d348563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348562 p = 1 := by simpa only [d348563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42556 p hg
    simpa only [d348563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42558 (p : Pattern) (guard : d348564 p = 1) : d51074 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348564, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42507 p hg
    simpa only [d348564, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348563 p = 1 := by simpa only [d348564, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42557 p hg
    simpa only [d348564, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42559 (p : Pattern) (guard : d348565 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348565, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42506 p hg
    simpa only [d348565, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348564 p = 1 := by simpa only [d348565, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42558 p hg
    simpa only [d348565, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42560 (p : Pattern) (guard : d348566 p = 1) : d51073 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348562 p = 1 := by simpa only [d348566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42556 p hg
    simpa only [d348566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42508 p hg
    simpa only [d348566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42561 (p : Pattern) (guard : d348567 p = 1) : d51074 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348567, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42507 p hg
    simpa only [d348567, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348566 p = 1 := by simpa only [d348567, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42560 p hg
    simpa only [d348567, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42562 (p : Pattern) (guard : d348568 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348568, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42506 p hg
    simpa only [d348568, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348567 p = 1 := by simpa only [d348568, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42561 p hg
    simpa only [d348568, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42563 (p : Pattern) (guard : d348569 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348565 p = 1 := by simpa only [d348569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42559 p hg
    simpa only [d348569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348568 p = 1 := by simpa only [d348569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42562 p hg
    simpa only [d348569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42564 (p : Pattern) (guard : d0 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42565 (p : Pattern) (guard : d348574 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348568 p = 1 := by simpa only [d348574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42562 p hg
    simpa only [d348574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42564 p hg
    simpa only [d348574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42566 (p : Pattern) (guard : d348575 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348569 p = 1 := by simpa only [d348575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42563 p hg
    simpa only [d348575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348574 p = 1 := by simpa only [d348575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42565 p hg
    simpa only [d348575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42567 (p : Pattern) (guard : d348576 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348575 p = 1 := by simpa only [d348576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42566 p hg
    simpa only [d348576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42564 p hg
    simpa only [d348576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42568 (p : Pattern) (guard : d0 p = 1) : d51076 p ≤ (0 : Int) + d47806 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42569 (p : Pattern) (guard : d348577 p = 1) : d51077 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348576 p = 1 := by simpa only [d348577, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42567 p hg
    simpa only [d348577, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348577, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42568 p hg
    simpa only [d348577, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42570 (p : Pattern) (guard : d348578 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348578, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42326 p hg
    simpa only [d348578, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348577 p = 1 := by simpa only [d348578, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42569 p hg
    simpa only [d348578, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42571 (p : Pattern) (guard : d348583 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348574 p = 1 := by simpa only [d348583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42565 p hg
    simpa only [d348583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42564 p hg
    simpa only [d348583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42572 (p : Pattern) (guard : d348584 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348583 p = 1 := by simpa only [d348584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42571 p hg
    simpa only [d348584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42564 p hg
    simpa only [d348584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42573 (p : Pattern) (guard : d348585 p = 1) : d51077 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348584 p = 1 := by simpa only [d348585, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42572 p hg
    simpa only [d348585, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348585, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42568 p hg
    simpa only [d348585, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42574 (p : Pattern) (guard : d348586 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348586, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42326 p hg
    simpa only [d348586, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348585 p = 1 := by simpa only [d348586, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42573 p hg
    simpa only [d348586, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42575 (p : Pattern) (guard : d348587 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348578 p = 1 := by simpa only [d348587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42570 p hg
    simpa only [d348587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348586 p = 1 := by simpa only [d348587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42574 p hg
    simpa only [d348587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42576 (p : Pattern) (guard : d348588 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348587 p = 1 := by simpa only [d348588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42575 p hg
    simpa only [d348588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d348588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42577 (p : Pattern) (guard : d348589 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348588 p = 1 := by simpa only [d348589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42576 p hg
    simpa only [d348589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d348589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42578 (p : Pattern) (guard : d348590 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348589 p = 1 := by simpa only [d348590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42577 p hg
    simpa only [d348590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d348590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42579 (p : Pattern) (guard : d348604 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348586 p = 1 := by simpa only [d348604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42574 p hg
    simpa only [d348604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d348604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42580 (p : Pattern) (guard : d348605 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348604 p = 1 := by simpa only [d348605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42579 p hg
    simpa only [d348605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d348605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42581 (p : Pattern) (guard : d348606 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348605 p = 1 := by simpa only [d348606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42580 p hg
    simpa only [d348606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d348606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42582 (p : Pattern) (guard : d348607 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348606 p = 1 := by simpa only [d348607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42581 p hg
    simpa only [d348607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d348607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42583 (p : Pattern) (guard : d349143 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348590 p = 1 := by simpa only [d349143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42578 p hg
    simpa only [d349143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348607 p = 1 := by simpa only [d349143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42582 p hg
    simpa only [d349143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42584 (p : Pattern) (guard : d349144 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d349144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349143 p = 1 := by simpa only [d349144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42583 p hg
    simpa only [d349144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42585 (p : Pattern) (guard : d349145 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d349144 p = 1 := by simpa only [d349145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42584 p hg
    simpa only [d349145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d349145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42586 (p : Pattern) (guard : d349146 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d349146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349145 p = 1 := by simpa only [d349146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42585 p hg
    simpa only [d349146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42587 (p : Pattern) (guard : d349147 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d349147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349146 p = 1 := by simpa only [d349147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42586 p hg
    simpa only [d349147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42588 (p : Pattern) (guard : d349148 p = 1) : d51079 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349148, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d349148, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349147 p = 1 := by simpa only [d349148, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42587 p hg
    simpa only [d349148, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42589 (p : Pattern) (guard : d349149 p = 1) : d51079 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42504 p hg
    simpa only [d349149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349148 p = 1 := by simpa only [d349149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42588 p hg
    simpa only [d349149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42590 (p : Pattern) (guard : d349150 p = 1) : d51079 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d349149 p = 1 := by simpa only [d349150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42589 p hg
    simpa only [d349150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42504 p hg
    simpa only [d349150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42591 (p : Pattern) (guard : d349151 p = 1) : d51079 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d349150 p = 1 := by simpa only [d349151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42590 p hg
    simpa only [d349151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42504 p hg
    simpa only [d349151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42592 (p : Pattern) (guard : d349152 p = 1) : d51079 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d349151 p = 1 := by simpa only [d349152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42591 p hg
    simpa only [d349152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42504 p hg
    simpa only [d349152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42593 (p : Pattern) (guard : d0 p = 1) : d51136 p ≤ (0 : Int) + d47864 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42594 (p : Pattern) (guard : d349153 p = 1) : d51137 p ≤ (0 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d349152 p = 1 := by simpa only [d349153, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42592 p hg
    simpa only [d349153, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349153, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42593 p hg
    simpa only [d349153, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42595 (p : Pattern) (guard : d349154 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d349142 p = 1 := by simpa only [d349154, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42503 p hg
    simpa only [d349154, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349153 p = 1 := by simpa only [d349154, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42594 p hg
    simpa only [d349154, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42596 (p : Pattern) (guard : d349155 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349154 p = 1 := by simpa only [d349155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42595 p hg
    simpa only [d349155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42597 (p : Pattern) (guard : d349156 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349155 p = 1 := by simpa only [d349156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42596 p hg
    simpa only [d349156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42598 (p : Pattern) (guard : d349157 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349156 p = 1 := by simpa only [d349157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42597 p hg
    simpa only [d349157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42599 (p : Pattern) (guard : d349158 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349157 p = 1 := by simpa only [d349158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42598 p hg
    simpa only [d349158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42600 (p : Pattern) (guard : d349159 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349158 p = 1 := by simpa only [d349159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42599 p hg
    simpa only [d349159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42601 (p : Pattern) (guard : d349160 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349159 p = 1 := by simpa only [d349160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42600 p hg
    simpa only [d349160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42602 (p : Pattern) (guard : d349161 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349160 p = 1 := by simpa only [d349161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42601 p hg
    simpa only [d349161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42603 (p : Pattern) (guard : d349162 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349161 p = 1 := by simpa only [d349162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42602 p hg
    simpa only [d349162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42604 (p : Pattern) (guard : d349163 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349162 p = 1 := by simpa only [d349163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42603 p hg
    simpa only [d349163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42605 (p : Pattern) (guard : d308 p = 1) : d4 p ≤ (0 : Int) + d4 p := by
  omega
theorem compare42606 (p : Pattern) (guard : d1519 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42605 p hg
    simpa only [d1519, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42333 p hg
    simpa only [d1519, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42607 (p : Pattern) (guard : d1531 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42606 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42608 (p : Pattern) (guard : d1547 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42607 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42609 (p : Pattern) (guard : d39244 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42608 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42610 (p : Pattern) (guard : d337457 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d39244 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42609 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42611 (p : Pattern) (guard : d337458 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d337457 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42610 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42612 (p : Pattern) (guard : d337473 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337458 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42611 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42613 (p : Pattern) (guard : d258107 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42609 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42614 (p : Pattern) (guard : d258108 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42613 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42615 (p : Pattern) (guard : d258109 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42614 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42616 (p : Pattern) (guard : d348629 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337473 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42612 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42615 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42617 (p : Pattern) (guard : d348630 p = 1) : d50840 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348629 p = 1 := by simpa only [d348630, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42616 p hg
    simpa only [d348630, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348630, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42345 p hg
    simpa only [d348630, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42618 (p : Pattern) (guard : d348631 p = 1) : d50840 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348630 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42617 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42347 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42619 (p : Pattern) (guard : d348632 p = 1) : d50881 p ≤ (0 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348631 p = 1 := by simpa only [d348632, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42618 p hg
    simpa only [d348632, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348632, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42349 p hg
    simpa only [d348632, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42620 (p : Pattern) (guard : d348633 p = 1) : d50884 p ≤ (0 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348632 p = 1 := by simpa only [d348633, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42619 p hg
    simpa only [d348633, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348633, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42351 p hg
    simpa only [d348633, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42621 (p : Pattern) (guard : d348634 p = 1) : d50907 p ≤ (0 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348634, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42330 p hg
    simpa only [d348634, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348633 p = 1 := by simpa only [d348634, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42620 p hg
    simpa only [d348634, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42622 (p : Pattern) (guard : d348635 p = 1) : d50911 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d348634 p = 1 := by simpa only [d348635, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42621 p hg
    simpa only [d348635, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348635, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42354 p hg
    simpa only [d348635, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42623 (p : Pattern) (guard : d348636 p = 1) : d50911 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42329 p hg
    simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348635 p = 1 := by simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42622 p hg
    simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42624 (p : Pattern) (guard : d348637 p = 1) : d50911 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42329 p hg
    simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348636 p = 1 := by simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42623 p hg
    simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42625 (p : Pattern) (guard : d348638 p = 1) : d50911 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d348635 p = 1 := by simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42622 p hg
    simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42329 p hg
    simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42626 (p : Pattern) (guard : d348639 p = 1) : d50911 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42329 p hg
    simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348638 p = 1 := by simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42625 p hg
    simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42627 (p : Pattern) (guard : d348640 p = 1) : d50911 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348637 p = 1 := by simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42624 p hg
    simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348639 p = 1 := by simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42626 p hg
    simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42628 (p : Pattern) (guard : d348641 p = 1) : d50912 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348641, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42328 p hg
    simpa only [d348641, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348640 p = 1 := by simpa only [d348641, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42627 p hg
    simpa only [d348641, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42629 (p : Pattern) (guard : d348642 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348642, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42327 p hg
    simpa only [d348642, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348641 p = 1 := by simpa only [d348642, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42628 p hg
    simpa only [d348642, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42630 (p : Pattern) (guard : d348643 p = 1) : d50911 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348639 p = 1 := by simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42626 p hg
    simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42329 p hg
    simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42631 (p : Pattern) (guard : d348644 p = 1) : d50912 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348644, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42328 p hg
    simpa only [d348644, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348643 p = 1 := by simpa only [d348644, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42630 p hg
    simpa only [d348644, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42632 (p : Pattern) (guard : d348645 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348645, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42327 p hg
    simpa only [d348645, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348644 p = 1 := by simpa only [d348645, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42631 p hg
    simpa only [d348645, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42633 (p : Pattern) (guard : d348646 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348642 p = 1 := by simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42629 p hg
    simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348645 p = 1 := by simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42632 p hg
    simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42634 (p : Pattern) (guard : d348647 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348645 p = 1 := by simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42632 p hg
    simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42367 p hg
    simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42635 (p : Pattern) (guard : d348648 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348646 p = 1 := by simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42633 p hg
    simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348647 p = 1 := by simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42634 p hg
    simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42636 (p : Pattern) (guard : d348649 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348648 p = 1 := by simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42635 p hg
    simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42367 p hg
    simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42637 (p : Pattern) (guard : d348650 p = 1) : d50953 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348649 p = 1 := by simpa only [d348650, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42636 p hg
    simpa only [d348650, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348650, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42371 p hg
    simpa only [d348650, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42638 (p : Pattern) (guard : d348651 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348651, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42326 p hg
    simpa only [d348651, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348650 p = 1 := by simpa only [d348651, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42637 p hg
    simpa only [d348651, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42639 (p : Pattern) (guard : d348652 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348647 p = 1 := by simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42634 p hg
    simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42367 p hg
    simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42640 (p : Pattern) (guard : d348653 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348652 p = 1 := by simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42639 p hg
    simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42367 p hg
    simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42641 (p : Pattern) (guard : d348654 p = 1) : d50953 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348653 p = 1 := by simpa only [d348654, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42640 p hg
    simpa only [d348654, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348654, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42371 p hg
    simpa only [d348654, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42642 (p : Pattern) (guard : d348655 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348655, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42326 p hg
    simpa only [d348655, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348654 p = 1 := by simpa only [d348655, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42641 p hg
    simpa only [d348655, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42643 (p : Pattern) (guard : d348656 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348651 p = 1 := by simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42638 p hg
    simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348655 p = 1 := by simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42642 p hg
    simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42644 (p : Pattern) (guard : d348657 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348656 p = 1 := by simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42643 p hg
    simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42645 (p : Pattern) (guard : d348658 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348657 p = 1 := by simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42644 p hg
    simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42646 (p : Pattern) (guard : d348659 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348658 p = 1 := by simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42645 p hg
    simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42647 (p : Pattern) (guard : d348660 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348655 p = 1 := by simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42642 p hg
    simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42648 (p : Pattern) (guard : d348661 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348660 p = 1 := by simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42647 p hg
    simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42649 (p : Pattern) (guard : d348662 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348661 p = 1 := by simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42648 p hg
    simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42650 (p : Pattern) (guard : d348663 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348662 p = 1 := by simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42649 p hg
    simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42651 (p : Pattern) (guard : d348664 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348659 p = 1 := by simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42646 p hg
    simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348663 p = 1 := by simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42650 p hg
    simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42652 (p : Pattern) (guard : d348665 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348664 p = 1 := by simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42651 p hg
    simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42653 (p : Pattern) (guard : d348666 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348665 p = 1 := by simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42652 p hg
    simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42654 (p : Pattern) (guard : d348667 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348666 p = 1 := by simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42653 p hg
    simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42655 (p : Pattern) (guard : d348668 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348667 p = 1 := by simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42654 p hg
    simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42656 (p : Pattern) (guard : d348669 p = 1) : d50955 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348669, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348669, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348668 p = 1 := by simpa only [d348669, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42655 p hg
    simpa only [d348669, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42657 (p : Pattern) (guard : d348642 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348642, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42393 p hg
    simpa only [d348642, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348641 p = 1 := by simpa only [d348642, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42628 p hg
    simpa only [d348642, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42658 (p : Pattern) (guard : d348645 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348645, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42393 p hg
    simpa only [d348645, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348644 p = 1 := by simpa only [d348645, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42631 p hg
    simpa only [d348645, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42659 (p : Pattern) (guard : d348646 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348642 p = 1 := by simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42657 p hg
    simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348645 p = 1 := by simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42658 p hg
    simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42660 (p : Pattern) (guard : d348647 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348645 p = 1 := by simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42658 p hg
    simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42397 p hg
    simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42661 (p : Pattern) (guard : d348648 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348646 p = 1 := by simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42659 p hg
    simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348647 p = 1 := by simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42660 p hg
    simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42662 (p : Pattern) (guard : d348649 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348648 p = 1 := by simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42661 p hg
    simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42397 p hg
    simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42663 (p : Pattern) (guard : d348650 p = 1) : d50932 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348649 p = 1 := by simpa only [d348650, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42662 p hg
    simpa only [d348650, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348650, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42371 p hg
    simpa only [d348650, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42664 (p : Pattern) (guard : d348651 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348651, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42392 p hg
    simpa only [d348651, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348650 p = 1 := by simpa only [d348651, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42663 p hg
    simpa only [d348651, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42665 (p : Pattern) (guard : d348652 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348647 p = 1 := by simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42660 p hg
    simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42397 p hg
    simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42666 (p : Pattern) (guard : d348653 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348652 p = 1 := by simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42665 p hg
    simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42397 p hg
    simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42667 (p : Pattern) (guard : d348654 p = 1) : d50932 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348653 p = 1 := by simpa only [d348654, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42666 p hg
    simpa only [d348654, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348654, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42371 p hg
    simpa only [d348654, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42668 (p : Pattern) (guard : d348655 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348655, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42392 p hg
    simpa only [d348655, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348654 p = 1 := by simpa only [d348655, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42667 p hg
    simpa only [d348655, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42669 (p : Pattern) (guard : d348656 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348651 p = 1 := by simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42664 p hg
    simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348655 p = 1 := by simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42668 p hg
    simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42670 (p : Pattern) (guard : d348657 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348656 p = 1 := by simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42669 p hg
    simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42671 (p : Pattern) (guard : d348658 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348657 p = 1 := by simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42670 p hg
    simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42672 (p : Pattern) (guard : d348659 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348658 p = 1 := by simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42671 p hg
    simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42673 (p : Pattern) (guard : d348660 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348655 p = 1 := by simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42668 p hg
    simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42674 (p : Pattern) (guard : d348661 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348660 p = 1 := by simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42673 p hg
    simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42675 (p : Pattern) (guard : d348662 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348661 p = 1 := by simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42674 p hg
    simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42676 (p : Pattern) (guard : d348663 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348662 p = 1 := by simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42675 p hg
    simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42677 (p : Pattern) (guard : d348664 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348659 p = 1 := by simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42672 p hg
    simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348663 p = 1 := by simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42676 p hg
    simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42678 (p : Pattern) (guard : d348665 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348664 p = 1 := by simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42677 p hg
    simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42679 (p : Pattern) (guard : d348666 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348665 p = 1 := by simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42678 p hg
    simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42680 (p : Pattern) (guard : d348667 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348666 p = 1 := by simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42679 p hg
    simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42681 (p : Pattern) (guard : d348668 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348667 p = 1 := by simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42680 p hg
    simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42682 (p : Pattern) (guard : d348672 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348658 p = 1 := by simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42645 p hg
    simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42683 (p : Pattern) (guard : d348673 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348662 p = 1 := by simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42649 p hg
    simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42684 (p : Pattern) (guard : d348674 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348672 p = 1 := by simpa only [d348674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42682 p hg
    simpa only [d348674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348673 p = 1 := by simpa only [d348674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42683 p hg
    simpa only [d348674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42685 (p : Pattern) (guard : d348675 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348674 p = 1 := by simpa only [d348675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42684 p hg
    simpa only [d348675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42686 (p : Pattern) (guard : d348676 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348675 p = 1 := by simpa only [d348676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42685 p hg
    simpa only [d348676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42687 (p : Pattern) (guard : d348677 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348676 p = 1 := by simpa only [d348677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42686 p hg
    simpa only [d348677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42688 (p : Pattern) (guard : d348678 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348677 p = 1 := by simpa only [d348678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42687 p hg
    simpa only [d348678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42689 (p : Pattern) (guard : d348679 p = 1) : d50955 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d348668 p = 1 := by simpa only [d348679, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42681 p hg
    simpa only [d348679, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348678 p = 1 := by simpa only [d348679, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42688 p hg
    simpa only [d348679, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42690 (p : Pattern) (guard : d348680 p = 1) : d50955 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d348669 p = 1 := by simpa only [d348680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42656 p hg
    simpa only [d348680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348679 p = 1 := by simpa only [d348680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42689 p hg
    simpa only [d348680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42691 (p : Pattern) (guard : d348681 p = 1) : d50955 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d348680 p = 1 := by simpa only [d348681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42690 p hg
    simpa only [d348681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42323 p hg
    simpa only [d348681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42692 (p : Pattern) (guard : d349164 p = 1) : d50955 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d348681 p = 1 := by simpa only [d349164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42691 p hg
    simpa only [d349164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42323 p hg
    simpa only [d349164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42693 (p : Pattern) (guard : d349165 p = 1) : d50955 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42323 p hg
    simpa only [d349165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349164 p = 1 := by simpa only [d349165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42692 p hg
    simpa only [d349165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42694 (p : Pattern) (guard : d308 p = 1) : d5 p ≤ (0 : Int) + d5 p := by
  omega
theorem compare42695 (p : Pattern) (guard : d1519 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42694 p hg
    simpa only [d1519, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42441 p hg
    simpa only [d1519, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42696 (p : Pattern) (guard : d1531 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42695 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42697 (p : Pattern) (guard : d1547 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42696 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42698 (p : Pattern) (guard : d39244 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42697 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42699 (p : Pattern) (guard : d337457 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d39244 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42698 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42700 (p : Pattern) (guard : d337458 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d337457 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42699 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42701 (p : Pattern) (guard : d337473 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337458 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42700 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42702 (p : Pattern) (guard : d258107 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42698 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42703 (p : Pattern) (guard : d258108 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42702 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42704 (p : Pattern) (guard : d258109 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42703 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42705 (p : Pattern) (guard : d348629 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337473 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42701 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42704 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42706 (p : Pattern) (guard : d348630 p = 1) : d50967 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348629 p = 1 := by simpa only [d348630, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42705 p hg
    simpa only [d348630, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348630, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42453 p hg
    simpa only [d348630, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42707 (p : Pattern) (guard : d348631 p = 1) : d50967 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348630 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42706 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42455 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42708 (p : Pattern) (guard : d348632 p = 1) : d50997 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348631 p = 1 := by simpa only [d348632, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42707 p hg
    simpa only [d348632, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348632, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42457 p hg
    simpa only [d348632, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42709 (p : Pattern) (guard : d348633 p = 1) : d50998 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348632 p = 1 := by simpa only [d348633, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42708 p hg
    simpa only [d348633, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348633, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d348633, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42710 (p : Pattern) (guard : d348634 p = 1) : d51018 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348634, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42438 p hg
    simpa only [d348634, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348633 p = 1 := by simpa only [d348634, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42709 p hg
    simpa only [d348634, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42711 (p : Pattern) (guard : d348635 p = 1) : d51022 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d348634 p = 1 := by simpa only [d348635, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42710 p hg
    simpa only [d348635, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348635, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42461 p hg
    simpa only [d348635, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42712 (p : Pattern) (guard : d348636 p = 1) : d51022 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42437 p hg
    simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348635 p = 1 := by simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42711 p hg
    simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42713 (p : Pattern) (guard : d348637 p = 1) : d51022 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42437 p hg
    simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348636 p = 1 := by simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42712 p hg
    simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42714 (p : Pattern) (guard : d348638 p = 1) : d51022 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d348635 p = 1 := by simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42711 p hg
    simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42437 p hg
    simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42715 (p : Pattern) (guard : d348639 p = 1) : d51022 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42437 p hg
    simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348638 p = 1 := by simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42714 p hg
    simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42716 (p : Pattern) (guard : d348640 p = 1) : d51022 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348637 p = 1 := by simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42713 p hg
    simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348639 p = 1 := by simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42715 p hg
    simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42717 (p : Pattern) (guard : d348641 p = 1) : d51023 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348641, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42436 p hg
    simpa only [d348641, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348640 p = 1 := by simpa only [d348641, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42716 p hg
    simpa only [d348641, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42718 (p : Pattern) (guard : d348642 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348642, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42435 p hg
    simpa only [d348642, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348641 p = 1 := by simpa only [d348642, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42717 p hg
    simpa only [d348642, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42719 (p : Pattern) (guard : d348643 p = 1) : d51022 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348639 p = 1 := by simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42715 p hg
    simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42437 p hg
    simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42720 (p : Pattern) (guard : d348644 p = 1) : d51023 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348644, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42436 p hg
    simpa only [d348644, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348643 p = 1 := by simpa only [d348644, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42719 p hg
    simpa only [d348644, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42721 (p : Pattern) (guard : d348645 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348645, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42435 p hg
    simpa only [d348645, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348644 p = 1 := by simpa only [d348645, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42720 p hg
    simpa only [d348645, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42722 (p : Pattern) (guard : d348646 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348642 p = 1 := by simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42718 p hg
    simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348645 p = 1 := by simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42721 p hg
    simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42723 (p : Pattern) (guard : d348647 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348645 p = 1 := by simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42721 p hg
    simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42474 p hg
    simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42724 (p : Pattern) (guard : d348648 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348646 p = 1 := by simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42722 p hg
    simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348647 p = 1 := by simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42723 p hg
    simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42725 (p : Pattern) (guard : d348649 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348648 p = 1 := by simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42724 p hg
    simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42474 p hg
    simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42726 (p : Pattern) (guard : d348650 p = 1) : d51036 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348649 p = 1 := by simpa only [d348650, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42725 p hg
    simpa only [d348650, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348650, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42478 p hg
    simpa only [d348650, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42727 (p : Pattern) (guard : d348651 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348651, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42434 p hg
    simpa only [d348651, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348650 p = 1 := by simpa only [d348651, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42726 p hg
    simpa only [d348651, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42728 (p : Pattern) (guard : d348652 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348647 p = 1 := by simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42723 p hg
    simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42474 p hg
    simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42729 (p : Pattern) (guard : d348653 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348652 p = 1 := by simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42728 p hg
    simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42474 p hg
    simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42730 (p : Pattern) (guard : d348654 p = 1) : d51036 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348653 p = 1 := by simpa only [d348654, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42729 p hg
    simpa only [d348654, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348654, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42478 p hg
    simpa only [d348654, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42731 (p : Pattern) (guard : d348655 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348655, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42434 p hg
    simpa only [d348655, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348654 p = 1 := by simpa only [d348655, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42730 p hg
    simpa only [d348655, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42732 (p : Pattern) (guard : d348656 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348651 p = 1 := by simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42727 p hg
    simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348655 p = 1 := by simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42731 p hg
    simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42733 (p : Pattern) (guard : d348657 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348656 p = 1 := by simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42732 p hg
    simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42734 (p : Pattern) (guard : d348658 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348657 p = 1 := by simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42733 p hg
    simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42735 (p : Pattern) (guard : d348672 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348658 p = 1 := by simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42734 p hg
    simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42736 (p : Pattern) (guard : d348660 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348655 p = 1 := by simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42731 p hg
    simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42737 (p : Pattern) (guard : d348661 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348660 p = 1 := by simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42736 p hg
    simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42738 (p : Pattern) (guard : d348662 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348661 p = 1 := by simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42737 p hg
    simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42739 (p : Pattern) (guard : d348673 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348662 p = 1 := by simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42738 p hg
    simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42740 (p : Pattern) (guard : d348674 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348672 p = 1 := by simpa only [d348674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42735 p hg
    simpa only [d348674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348673 p = 1 := by simpa only [d348674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42739 p hg
    simpa only [d348674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42741 (p : Pattern) (guard : d348675 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348674 p = 1 := by simpa only [d348675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42740 p hg
    simpa only [d348675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42742 (p : Pattern) (guard : d348676 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348675 p = 1 := by simpa only [d348676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42741 p hg
    simpa only [d348676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42743 (p : Pattern) (guard : d348677 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348676 p = 1 := by simpa only [d348677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42742 p hg
    simpa only [d348677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42744 (p : Pattern) (guard : d348678 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348677 p = 1 := by simpa only [d348678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42743 p hg
    simpa only [d348678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42745 (p : Pattern) (guard : d349166 p = 1) : d51038 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349166, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d349166, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348678 p = 1 := by simpa only [d349166, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42744 p hg
    simpa only [d349166, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42746 (p : Pattern) (guard : d349167 p = 1) : d51038 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42432 p hg
    simpa only [d349167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349166 p = 1 := by simpa only [d349167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42745 p hg
    simpa only [d349167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42747 (p : Pattern) (guard : d349168 p = 1) : d51038 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d349167 p = 1 := by simpa only [d349168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42746 p hg
    simpa only [d349168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42432 p hg
    simpa only [d349168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42748 (p : Pattern) (guard : d349169 p = 1) : d51038 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d349168 p = 1 := by simpa only [d349169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42747 p hg
    simpa only [d349169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42432 p hg
    simpa only [d349169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42749 (p : Pattern) (guard : d349170 p = 1) : d51038 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d349169 p = 1 := by simpa only [d349170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42748 p hg
    simpa only [d349170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42432 p hg
    simpa only [d349170, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
