import NetHack.Soko22Hazard87.Compare065
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare16500 (p : Pattern) (guard : d27 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare16501 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d48140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16502 (p : Pattern) (guard : d28 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16500 p hg
    simpa only [d28, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d28, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16503 (p : Pattern) (guard : d0 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16504 (p : Pattern) (guard : d29 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16502 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16505 (p : Pattern) (guard : d30 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16504 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16506 (p : Pattern) (guard : d31 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16505 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16507 (p : Pattern) (guard : d32 p = 1) : d48326 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16499 p hg
    simpa only [d32, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31 p = 1 := by simpa only [d32, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16506 p hg
    simpa only [d32, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16508 (p : Pattern) (guard : d33 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d33, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16507 p hg
    simpa only [d33, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16509 (p : Pattern) (guard : d0 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16510 (p : Pattern) (guard : d34 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16508 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16511 (p : Pattern) (guard : d35 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16510 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16512 (p : Pattern) (guard : d36 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16511 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16513 (p : Pattern) (guard : d0 p = 1) : d48328 p ≤ (0 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16514 (p : Pattern) (guard : d37 p = 1) : d48338 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16512 p hg
    simpa only [d37, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d37, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16515 (p : Pattern) (guard : d38 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d38, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16514 p hg
    simpa only [d38, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16516 (p : Pattern) (guard : d39 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16515 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16517 (p : Pattern) (guard : d40 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16516 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16518 (p : Pattern) (guard : d41 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16517 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16519 (p : Pattern) (guard : d42 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d41 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16518 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16520 (p : Pattern) (guard : d43 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d42 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16519 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16521 (p : Pattern) (guard : d100 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16520 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16522 (p : Pattern) (guard : d101 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d100 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16521 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16523 (p : Pattern) (guard : d102 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16522 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16524 (p : Pattern) (guard : d103 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16523 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16525 (p : Pattern) (guard : d104 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d103 p = 1 := by simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16524 p hg
    simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16526 (p : Pattern) (guard : d0 p = 1) : d48321 p ≤ (0 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16527 (p : Pattern) (guard : d0 p = 1) : d48324 p ≤ (0 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16528 (p : Pattern) (guard : d33 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16527 p hg
    simpa only [d33, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16507 p hg
    simpa only [d33, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16529 (p : Pattern) (guard : d0 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16530 (p : Pattern) (guard : d34 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16528 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16531 (p : Pattern) (guard : d35 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16530 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16532 (p : Pattern) (guard : d36 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16531 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16533 (p : Pattern) (guard : d37 p = 1) : d48329 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16532 p hg
    simpa only [d37, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d37, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16534 (p : Pattern) (guard : d38 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16526 p hg
    simpa only [d38, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16533 p hg
    simpa only [d38, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16535 (p : Pattern) (guard : d39 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16534 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16536 (p : Pattern) (guard : d40 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16535 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16537 (p : Pattern) (guard : d41 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16536 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16538 (p : Pattern) (guard : d42 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d41 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16537 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16539 (p : Pattern) (guard : d43 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d42 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16538 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16540 (p : Pattern) (guard : d100 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16539 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16541 (p : Pattern) (guard : d101 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d100 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16540 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16542 (p : Pattern) (guard : d102 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16541 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16543 (p : Pattern) (guard : d103 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16542 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16544 (p : Pattern) (guard : d49 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d41 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16518 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16545 (p : Pattern) (guard : d50 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d49 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16544 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16546 (p : Pattern) (guard : d107 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d50 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16545 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16547 (p : Pattern) (guard : d108 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d107 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16546 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16548 (p : Pattern) (guard : d109 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d108 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16547 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16549 (p : Pattern) (guard : d110 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d109 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16548 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16550 (p : Pattern) (guard : d111 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d103 p = 1 := by simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16543 p hg
    simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d110 p = 1 := by simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16549 p hg
    simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16551 (p : Pattern) (guard : d112 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d104 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16525 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d111 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16550 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16552 (p : Pattern) (guard : d113 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d112 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16551 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16553 (p : Pattern) (guard : d53637 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d113 p = 1 := by simpa only [d53637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16552 p hg
    simpa only [d53637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d53637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16554 (p : Pattern) (guard : d53638 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d53638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53637 p = 1 := by simpa only [d53638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16553 p hg
    simpa only [d53638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16555 (p : Pattern) (guard : d0 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16556 (p : Pattern) (guard : d0 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16557 (p : Pattern) (guard : d0 p = 1) : d48351 p ≤ (0 : Int) + d48178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16558 (p : Pattern) (guard : d0 p = 1) : d48353 p ≤ (0 : Int) + d48178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16559 (p : Pattern) (guard : d0 p = 1) : d48344 p ≤ (0 : Int) + d48168 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16560 (p : Pattern) (guard : d27 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare16561 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d48176 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16562 (p : Pattern) (guard : d28 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16560 p hg
    simpa only [d28, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d28, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16563 (p : Pattern) (guard : d0 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16564 (p : Pattern) (guard : d29 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16562 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16565 (p : Pattern) (guard : d30 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16564 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16566 (p : Pattern) (guard : d31 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16565 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16567 (p : Pattern) (guard : d32 p = 1) : d48346 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16559 p hg
    simpa only [d32, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31 p = 1 := by simpa only [d32, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16566 p hg
    simpa only [d32, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16568 (p : Pattern) (guard : d33 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16558 p hg
    simpa only [d33, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16567 p hg
    simpa only [d33, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16569 (p : Pattern) (guard : d0 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16570 (p : Pattern) (guard : d34 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16568 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16571 (p : Pattern) (guard : d35 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16570 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16572 (p : Pattern) (guard : d36 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16571 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16573 (p : Pattern) (guard : d0 p = 1) : d48355 p ≤ (0 : Int) + d48178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16574 (p : Pattern) (guard : d37 p = 1) : d48356 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16572 p hg
    simpa only [d37, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16573 p hg
    simpa only [d37, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16575 (p : Pattern) (guard : d38 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16557 p hg
    simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16574 p hg
    simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16576 (p : Pattern) (guard : d39 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16575 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16577 (p : Pattern) (guard : d40 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16576 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16578 (p : Pattern) (guard : d41 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16577 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16579 (p : Pattern) (guard : d49 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d41 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16578 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16580 (p : Pattern) (guard : d50 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d49 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16579 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16581 (p : Pattern) (guard : d107 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d50 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16580 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16582 (p : Pattern) (guard : d108 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d107 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16581 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16583 (p : Pattern) (guard : d109 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d108 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16582 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16584 (p : Pattern) (guard : d110 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d109 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16583 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16585 (p : Pattern) (guard : d406 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d406, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d406, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d110 p = 1 := by simpa only [d406, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16584 p hg
    simpa only [d406, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16586 (p : Pattern) (guard : d407 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d406 p = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16585 p hg
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16587 (p : Pattern) (guard : d53639 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 69 with
  | false =>
    have hg : d407 p = 1 := by simpa only [d53639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16586 p hg
    simpa only [d53639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d53639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16588 (p : Pattern) (guard : d53640 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53639 p = 1 := by simpa only [d53640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16587 p hg
    simpa only [d53640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d53640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16589 (p : Pattern) (guard : d53641 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53640 p = 1 := by simpa only [d53641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16588 p hg
    simpa only [d53641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d53641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16590 (p : Pattern) (guard : d53642 p = 1) : d48359 p ≤ (0 : Int) + d171289 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53638 p = 1 := by simpa only [d53642, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16554 p hg
    simpa only [d53642, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53641 p = 1 := by simpa only [d53642, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16589 p hg
    simpa only [d53642, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16591 (p : Pattern) (guard : d0 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16592 (p : Pattern) (guard : d0 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16593 (p : Pattern) (guard : d0 p = 1) : d48317 p ≤ (0 : Int) + d48204 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16594 (p : Pattern) (guard : d0 p = 1) : d48360 p ≤ (0 : Int) + d48195 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16595 (p : Pattern) (guard : d68 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare16596 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d48202 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16597 (p : Pattern) (guard : d69 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d68 p = 1 := by simpa only [d69, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16595 p hg
    simpa only [d69, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d69, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d69, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16598 (p : Pattern) (guard : d0 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16599 (p : Pattern) (guard : d70 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d69 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16597 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16600 (p : Pattern) (guard : d71 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d70 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16599 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16601 (p : Pattern) (guard : d72 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d71 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16600 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16602 (p : Pattern) (guard : d73 p = 1) : d48362 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d73, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16594 p hg
    simpa only [d73, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72 p = 1 := by simpa only [d73, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16601 p hg
    simpa only [d73, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16603 (p : Pattern) (guard : d74 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d74, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d74, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d73 p = 1 := by simpa only [d74, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16602 p hg
    simpa only [d74, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16604 (p : Pattern) (guard : d0 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16605 (p : Pattern) (guard : d75 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d74 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16603 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16606 (p : Pattern) (guard : d76 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d75 p = 1 := by simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16605 p hg
    simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16607 (p : Pattern) (guard : d77 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d76 p = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16606 p hg
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16608 (p : Pattern) (guard : d0 p = 1) : d48364 p ≤ (0 : Int) + d48204 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16609 (p : Pattern) (guard : d78 p = 1) : d48365 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d77 p = 1 := by simpa only [d78, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16607 p hg
    simpa only [d78, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d78, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16608 p hg
    simpa only [d78, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16610 (p : Pattern) (guard : d79 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d79, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d79, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d78 p = 1 := by simpa only [d79, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16609 p hg
    simpa only [d79, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16611 (p : Pattern) (guard : d80 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d79 p = 1 := by simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16610 p hg
    simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16612 (p : Pattern) (guard : d81 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d80 p = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16611 p hg
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16613 (p : Pattern) (guard : d82 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d81 p = 1 := by simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16612 p hg
    simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16614 (p : Pattern) (guard : d83 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d82 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16613 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16615 (p : Pattern) (guard : d84 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d83 p = 1 := by simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16614 p hg
    simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16616 (p : Pattern) (guard : d458 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d84 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16615 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16617 (p : Pattern) (guard : d459 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d458 p = 1 := by simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16616 p hg
    simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16618 (p : Pattern) (guard : d460 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d459 p = 1 := by simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16617 p hg
    simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16619 (p : Pattern) (guard : d461 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d460 p = 1 := by simpa only [d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16618 p hg
    simpa only [d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16620 (p : Pattern) (guard : d462 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d462, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d462, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d461 p = 1 := by simpa only [d462, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16619 p hg
    simpa only [d462, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16621 (p : Pattern) (guard : d463 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d462 p = 1 := by simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16620 p hg
    simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16622 (p : Pattern) (guard : d53643 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 69 with
  | false =>
    have hg : d463 p = 1 := by simpa only [d53643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16621 p hg
    simpa only [d53643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d53643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16623 (p : Pattern) (guard : d53644 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53643 p = 1 := by simpa only [d53644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16622 p hg
    simpa only [d53644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d53644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16624 (p : Pattern) (guard : d53645 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53644 p = 1 := by simpa only [d53645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16623 p hg
    simpa only [d53645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d53645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16625 (p : Pattern) (guard : d0 p = 1) : d48386 p ≤ (0 : Int) + d171293 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16626 (p : Pattern) (guard : d53646 p = 1) : d48387 p ≤ (0 : Int) + d171294 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53645 p = 1 := by simpa only [d53646, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16624 p hg
    simpa only [d53646, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53646, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16625 p hg
    simpa only [d53646, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16627 (p : Pattern) (guard : d53647 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 48 with
  | false =>
    have hg : d53642 p = 1 := by simpa only [d53647, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16590 p hg
    simpa only [d53647, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53646 p = 1 := by simpa only [d53647, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16626 p hg
    simpa only [d53647, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16628 (p : Pattern) (guard : d53648 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d53648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53647 p = 1 := by simpa only [d53648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16627 p hg
    simpa only [d53648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16629 (p : Pattern) (guard : d53649 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d53649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53648 p = 1 := by simpa only [d53649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16628 p hg
    simpa only [d53649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16630 (p : Pattern) (guard : d53650 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d53650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53649 p = 1 := by simpa only [d53650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16629 p hg
    simpa only [d53650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16631 (p : Pattern) (guard : d53651 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d53651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53650 p = 1 := by simpa only [d53651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16630 p hg
    simpa only [d53651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16632 (p : Pattern) (guard : d53652 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d53652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53651 p = 1 := by simpa only [d53652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16631 p hg
    simpa only [d53652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16633 (p : Pattern) (guard : d141 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare16634 (p : Pattern) (guard : d142 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16633 p hg
    simpa only [d142, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d142, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16635 (p : Pattern) (guard : d143 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16634 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16502 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16636 (p : Pattern) (guard : d144 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16635 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16504 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16637 (p : Pattern) (guard : d145 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16636 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16505 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16638 (p : Pattern) (guard : d146 p = 1) : d48326 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d146, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16499 p hg
    simpa only [d146, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d145 p = 1 := by simpa only [d146, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16637 p hg
    simpa only [d146, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16639 (p : Pattern) (guard : d147 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d147, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16638 p hg
    simpa only [d147, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16640 (p : Pattern) (guard : d148 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16639 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16508 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16641 (p : Pattern) (guard : d149 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16640 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16510 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16642 (p : Pattern) (guard : d150 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16641 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16643 (p : Pattern) (guard : d151 p = 1) : d48338 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16642 p hg
    simpa only [d151, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d151, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16644 (p : Pattern) (guard : d152 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d152, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16643 p hg
    simpa only [d152, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16645 (p : Pattern) (guard : d153 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16644 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16515 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16646 (p : Pattern) (guard : d154 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16645 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16647 (p : Pattern) (guard : d155 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16646 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16648 (p : Pattern) (guard : d156 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d155 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16647 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16649 (p : Pattern) (guard : d157 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d156 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16648 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16519 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16650 (p : Pattern) (guard : d280 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d157 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16649 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16651 (p : Pattern) (guard : d281 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d280 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16650 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16652 (p : Pattern) (guard : d282 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d281 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16651 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16653 (p : Pattern) (guard : d283 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d282 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16652 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16654 (p : Pattern) (guard : d284 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d283 p = 1 := by simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16653 p hg
    simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16655 (p : Pattern) (guard : d147 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16527 p hg
    simpa only [d147, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16638 p hg
    simpa only [d147, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16656 (p : Pattern) (guard : d148 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16655 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16528 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16657 (p : Pattern) (guard : d149 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16656 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16530 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16658 (p : Pattern) (guard : d150 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16657 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16659 (p : Pattern) (guard : d151 p = 1) : d48329 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16658 p hg
    simpa only [d151, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d151, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16660 (p : Pattern) (guard : d152 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16526 p hg
    simpa only [d152, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16659 p hg
    simpa only [d152, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16661 (p : Pattern) (guard : d153 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16660 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16534 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16662 (p : Pattern) (guard : d154 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16661 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16663 (p : Pattern) (guard : d155 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16662 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16664 (p : Pattern) (guard : d156 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d155 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16663 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16665 (p : Pattern) (guard : d157 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d156 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16664 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16538 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16666 (p : Pattern) (guard : d280 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d157 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16665 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16667 (p : Pattern) (guard : d281 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d280 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16666 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16668 (p : Pattern) (guard : d282 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d281 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16667 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16669 (p : Pattern) (guard : d283 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d282 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16668 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16670 (p : Pattern) (guard : d203 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d155 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16647 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16671 (p : Pattern) (guard : d204 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d203 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16670 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d49 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16544 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16672 (p : Pattern) (guard : d287 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d204 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16671 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16673 (p : Pattern) (guard : d288 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d287 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16672 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16674 (p : Pattern) (guard : d289 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d288 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16673 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16675 (p : Pattern) (guard : d290 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d289 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16674 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16676 (p : Pattern) (guard : d291 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d283 p = 1 := by simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16669 p hg
    simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d290 p = 1 := by simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16675 p hg
    simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16677 (p : Pattern) (guard : d292 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d284 p = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16654 p hg
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d291 p = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16676 p hg
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16678 (p : Pattern) (guard : d293 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d292 p = 1 := by simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16677 p hg
    simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16679 (p : Pattern) (guard : d53653 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d293 p = 1 := by simpa only [d53653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16678 p hg
    simpa only [d53653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d53653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16680 (p : Pattern) (guard : d53654 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d53654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53653 p = 1 := by simpa only [d53654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16679 p hg
    simpa only [d53654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16681 (p : Pattern) (guard : d141 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare16682 (p : Pattern) (guard : d142 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16681 p hg
    simpa only [d142, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d142, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16683 (p : Pattern) (guard : d143 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16682 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16562 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16684 (p : Pattern) (guard : d144 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16683 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16564 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16685 (p : Pattern) (guard : d145 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16684 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16565 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16686 (p : Pattern) (guard : d146 p = 1) : d48346 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d146, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16559 p hg
    simpa only [d146, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d145 p = 1 := by simpa only [d146, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16685 p hg
    simpa only [d146, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16687 (p : Pattern) (guard : d147 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16558 p hg
    simpa only [d147, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16686 p hg
    simpa only [d147, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16688 (p : Pattern) (guard : d148 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16687 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16568 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16689 (p : Pattern) (guard : d149 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16688 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16570 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16690 (p : Pattern) (guard : d150 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16689 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16691 (p : Pattern) (guard : d151 p = 1) : d48356 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16690 p hg
    simpa only [d151, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16573 p hg
    simpa only [d151, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16692 (p : Pattern) (guard : d152 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16557 p hg
    simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16691 p hg
    simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16693 (p : Pattern) (guard : d153 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16692 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16575 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16694 (p : Pattern) (guard : d154 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16693 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16695 (p : Pattern) (guard : d155 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16694 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16696 (p : Pattern) (guard : d203 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d155 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16695 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16697 (p : Pattern) (guard : d204 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d203 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16696 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d49 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16579 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16698 (p : Pattern) (guard : d287 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d204 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16697 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16699 (p : Pattern) (guard : d288 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d287 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16698 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16700 (p : Pattern) (guard : d289 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d288 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16699 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16701 (p : Pattern) (guard : d290 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d289 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16700 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16702 (p : Pattern) (guard : d53655 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53655, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d53655, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d290 p = 1 := by simpa only [d53655, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16701 p hg
    simpa only [d53655, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16703 (p : Pattern) (guard : d53656 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d53656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53655 p = 1 := by simpa only [d53656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16702 p hg
    simpa only [d53656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16704 (p : Pattern) (guard : d53657 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 69 with
  | false =>
    have hg : d53656 p = 1 := by simpa only [d53657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16703 p hg
    simpa only [d53657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d53657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16705 (p : Pattern) (guard : d53658 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53657 p = 1 := by simpa only [d53658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16704 p hg
    simpa only [d53658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d53658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16706 (p : Pattern) (guard : d53659 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53658 p = 1 := by simpa only [d53659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16705 p hg
    simpa only [d53659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d53659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16707 (p : Pattern) (guard : d53660 p = 1) : d48359 p ≤ (0 : Int) + d171289 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53654 p = 1 := by simpa only [d53660, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16680 p hg
    simpa only [d53660, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53659 p = 1 := by simpa only [d53660, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16706 p hg
    simpa only [d53660, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16708 (p : Pattern) (guard : d228 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare16709 (p : Pattern) (guard : d229 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d228 p = 1 := by simpa only [d229, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16708 p hg
    simpa only [d229, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d229, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d229, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16710 (p : Pattern) (guard : d230 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d229 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16709 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d69 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16597 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16711 (p : Pattern) (guard : d231 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d230 p = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16710 p hg
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d70 p = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16599 p hg
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16712 (p : Pattern) (guard : d232 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d231 p = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16711 p hg
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d71 p = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16600 p hg
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16713 (p : Pattern) (guard : d233 p = 1) : d48362 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d233, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16594 p hg
    simpa only [d233, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d232 p = 1 := by simpa only [d233, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16712 p hg
    simpa only [d233, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16714 (p : Pattern) (guard : d234 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d234, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d234, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d233 p = 1 := by simpa only [d234, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16713 p hg
    simpa only [d234, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16715 (p : Pattern) (guard : d235 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d234 p = 1 := by simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16714 p hg
    simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d74 p = 1 := by simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16603 p hg
    simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16716 (p : Pattern) (guard : d236 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d235 p = 1 := by simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16715 p hg
    simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d75 p = 1 := by simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16605 p hg
    simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16717 (p : Pattern) (guard : d237 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d236 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16716 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16718 (p : Pattern) (guard : d238 p = 1) : d48365 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d237 p = 1 := by simpa only [d238, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16717 p hg
    simpa only [d238, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d238, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16608 p hg
    simpa only [d238, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16719 (p : Pattern) (guard : d239 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d239, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d239, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d238 p = 1 := by simpa only [d239, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16718 p hg
    simpa only [d239, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16720 (p : Pattern) (guard : d240 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d239 p = 1 := by simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16719 p hg
    simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d79 p = 1 := by simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16610 p hg
    simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16721 (p : Pattern) (guard : d241 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d240 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16720 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16722 (p : Pattern) (guard : d242 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d241 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16721 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16723 (p : Pattern) (guard : d243 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d242 p = 1 := by simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16722 p hg
    simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16724 (p : Pattern) (guard : d244 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d243 p = 1 := by simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16723 p hg
    simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d83 p = 1 := by simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16614 p hg
    simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16725 (p : Pattern) (guard : d53661 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d53661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d244 p = 1 := by simpa only [d53661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16724 p hg
    simpa only [d53661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16726 (p : Pattern) (guard : d53662 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d53661 p = 1 := by simpa only [d53662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16725 p hg
    simpa only [d53662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d53662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16727 (p : Pattern) (guard : d53663 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d53663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53662 p = 1 := by simpa only [d53663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16726 p hg
    simpa only [d53663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16728 (p : Pattern) (guard : d53664 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d53664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53663 p = 1 := by simpa only [d53664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16727 p hg
    simpa only [d53664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16729 (p : Pattern) (guard : d53665 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53665, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d53665, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53664 p = 1 := by simpa only [d53665, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16728 p hg
    simpa only [d53665, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16730 (p : Pattern) (guard : d53666 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d53666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53665 p = 1 := by simpa only [d53666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16729 p hg
    simpa only [d53666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16731 (p : Pattern) (guard : d53667 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 69 with
  | false =>
    have hg : d53666 p = 1 := by simpa only [d53667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16730 p hg
    simpa only [d53667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d53667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16732 (p : Pattern) (guard : d53668 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53667 p = 1 := by simpa only [d53668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16731 p hg
    simpa only [d53668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d53668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16733 (p : Pattern) (guard : d53669 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53668 p = 1 := by simpa only [d53669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16732 p hg
    simpa only [d53669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d53669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16734 (p : Pattern) (guard : d53670 p = 1) : d48387 p ≤ (0 : Int) + d171294 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53669 p = 1 := by simpa only [d53670, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16733 p hg
    simpa only [d53670, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53670, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16625 p hg
    simpa only [d53670, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16735 (p : Pattern) (guard : d53671 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 48 with
  | false =>
    have hg : d53660 p = 1 := by simpa only [d53671, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16707 p hg
    simpa only [d53671, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53670 p = 1 := by simpa only [d53671, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16734 p hg
    simpa only [d53671, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16736 (p : Pattern) (guard : d53672 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d53672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53671 p = 1 := by simpa only [d53672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16735 p hg
    simpa only [d53672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16737 (p : Pattern) (guard : d53673 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d53673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53672 p = 1 := by simpa only [d53673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16736 p hg
    simpa only [d53673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16738 (p : Pattern) (guard : d53674 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d53674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53673 p = 1 := by simpa only [d53674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16737 p hg
    simpa only [d53674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16739 (p : Pattern) (guard : d53675 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d53675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53674 p = 1 := by simpa only [d53675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16738 p hg
    simpa only [d53675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16740 (p : Pattern) (guard : d53676 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d53676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53675 p = 1 := by simpa only [d53676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16739 p hg
    simpa only [d53676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16741 (p : Pattern) (guard : d53677 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d53652 p = 1 := by simpa only [d53677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16632 p hg
    simpa only [d53677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53676 p = 1 := by simpa only [d53677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16740 p hg
    simpa only [d53677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16742 (p : Pattern) (guard : d321 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare16743 (p : Pattern) (guard : d322 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16742 p hg
    simpa only [d322, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d322, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16744 (p : Pattern) (guard : d323 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16743 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16634 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16745 (p : Pattern) (guard : d12493 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare16746 (p : Pattern) (guard : d12494 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12493 p = 1 := by simpa only [d12494, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16745 p hg
    simpa only [d12494, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12494, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d12494, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16747 (p : Pattern) (guard : d12495 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12494 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16746 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16502 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16748 (p : Pattern) (guard : d15966 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16744 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12495 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16747 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16749 (p : Pattern) (guard : d15967 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16748 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16636 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
