/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons060
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8540 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d60 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8541 (p : Pattern) (guard : d4765 p = 1) : d1059 p ≤ (4 : Int) + d4333 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1059, d4333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8518 p hg
    simpa only [d4765, d1059, d4333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1059, d4333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8540 p hg
    simpa only [d4765, d1059, d4333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8542 (p : Pattern) (guard : d4765 p = 1) : d1060 p ≤ (4 : Int) + d4334 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1060, d4334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8539 p hg
    simpa only [d1060, d4334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1060, d4334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8541 p hg
    simpa only [d1060, d4334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8543 (p : Pattern) (guard : d4765 p = 1) : d1062 p ≤ (4 : Int) + d1062 p := by
  omega
theorem compare8544 (p : Pattern) (guard : d4765 p = 1) : d1063 p ≤ (4 : Int) + d4346 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1063, d4346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8542 p hg
    simpa only [d1063, d4346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1063, d4346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8543 p hg
    simpa only [d1063, d4346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8545 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8546 (p : Pattern) (guard : d4765 p = 1) : d1059 p ≤ (4 : Int) + d4339 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1059, d4339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8518 p hg
    simpa only [d4765, d1059, d4339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1059, d4339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8545 p hg
    simpa only [d4765, d1059, d4339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8547 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (4 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8523 p hg
    simpa only [d109, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8524 p hg
    simpa only [d109, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8548 (p : Pattern) (guard : d4147 p = 1) : d873 p ≤ (4 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3982 p hg
    simpa only [d4147, d873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8547 p hg
    simpa only [d4147, d873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8549 (p : Pattern) (guard : d4765 p = 1) : d1064 p ≤ (4 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1064, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8548 p hg
    simpa only [d4765, d1064, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1064, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d4765, d1064, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8550 (p : Pattern) (guard : d4765 p = 1) : d1065 p ≤ (4 : Int) + d4340 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1065, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8546 p hg
    simpa only [d1065, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1065, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8549 p hg
    simpa only [d1065, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8551 (p : Pattern) (guard : d4765 p = 1) : d1066 p ≤ (4 : Int) + d1062 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1066, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8549 p hg
    simpa only [d1066, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1066, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8408 p hg
    simpa only [d1066, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8552 (p : Pattern) (guard : d4765 p = 1) : d1067 p ≤ (4 : Int) + d4347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1067, d4347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8550 p hg
    simpa only [d1067, d4347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1067, d4347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8551 p hg
    simpa only [d1067, d4347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8553 (p : Pattern) (guard : d4765 p = 1) : d1068 p ≤ (4 : Int) + d4348 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1068, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8544 p hg
    simpa only [d1068, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1068, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8552 p hg
    simpa only [d1068, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8554 (p : Pattern) (guard : d4765 p = 1) : d1069 p ≤ (4 : Int) + d4349 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1069, d4349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8537 p hg
    simpa only [d1069, d4349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1069, d4349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8553 p hg
    simpa only [d1069, d4349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8555 (p : Pattern) (guard : d0 p = 1) : d361 p ≤ (4 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8556 (p : Pattern) (guard : d4765 p = 1) : d1070 p ≤ (4 : Int) + d105 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3960 p hg
    simpa only [d4765, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8555 p hg
    simpa only [d4765, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8557 (p : Pattern) (guard : d4765 p = 1) : d1071 p ≤ (4 : Int) + d4334 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1071, d4334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8556 p hg
    simpa only [d1071, d4334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1071, d4334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8541 p hg
    simpa only [d1071, d4334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8558 (p : Pattern) (guard : d4765 p = 1) : d1072 p ≤ (4 : Int) + d4346 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1072, d4346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8557 p hg
    simpa only [d1072, d4346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1072, d4346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8543 p hg
    simpa only [d1072, d4346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8559 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (4 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8560 (p : Pattern) (guard : d4765 p = 1) : d1073 p ≤ (4 : Int) + d4339 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1073, d4339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8518 p hg
    simpa only [d4765, d1073, d4339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1073, d4339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8559 p hg
    simpa only [d4765, d1073, d4339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8561 (p : Pattern) (guard : d4765 p = 1) : d1074 p ≤ (4 : Int) + d4340 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1074, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8560 p hg
    simpa only [d1074, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1074, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8549 p hg
    simpa only [d1074, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8562 (p : Pattern) (guard : d4765 p = 1) : d1075 p ≤ (4 : Int) + d4347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1075, d4347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8561 p hg
    simpa only [d1075, d4347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1075, d4347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8551 p hg
    simpa only [d1075, d4347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8563 (p : Pattern) (guard : d4765 p = 1) : d1076 p ≤ (4 : Int) + d4348 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1076, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8558 p hg
    simpa only [d1076, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1076, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8562 p hg
    simpa only [d1076, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8564 (p : Pattern) (guard : d4765 p = 1) : d159 p ≤ (4 : Int) + d4350 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d159, d4350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3965 p hg
    simpa only [d4765, d159, d4350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d159, d4350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d4765, d159, d4350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8565 (p : Pattern) (guard : d4765 p = 1) : d160 p ≤ (4 : Int) + d4351 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d160, d4351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8564 p hg
    simpa only [d160, d4351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d160, d4351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8408 p hg
    simpa only [d160, d4351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8566 (p : Pattern) (guard : d4765 p = 1) : d161 p ≤ (4 : Int) + d4352 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d161, d4352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8565 p hg
    simpa only [d161, d4352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d161, d4352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8408 p hg
    simpa only [d161, d4352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8567 (p : Pattern) (guard : d4765 p = 1) : d162 p ≤ (4 : Int) + d4353 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d162, d4353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8566 p hg
    simpa only [d162, d4353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d162, d4353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8408 p hg
    simpa only [d162, d4353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8568 (p : Pattern) (guard : d4765 p = 1) : d1077 p ≤ (4 : Int) + d4354 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1077, d4354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8563 p hg
    simpa only [d1077, d4354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1077, d4354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8567 p hg
    simpa only [d1077, d4354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8569 (p : Pattern) (guard : d4765 p = 1) : d1078 p ≤ (4 : Int) + d4355 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1078, d4355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8554 p hg
    simpa only [d1078, d4355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1078, d4355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8568 p hg
    simpa only [d1078, d4355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8570 (p : Pattern) (guard : d0 p = 1) : d389 p ≤ (4 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8571 (p : Pattern) (guard : d4765 p = 1) : d1079 p ≤ (4 : Int) + d105 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3960 p hg
    simpa only [d4765, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8570 p hg
    simpa only [d4765, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8572 (p : Pattern) (guard : d4765 p = 1) : d1080 p ≤ (4 : Int) + d4333 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1080, d4333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8507 p hg
    simpa only [d4765, d1080, d4333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1080, d4333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8540 p hg
    simpa only [d4765, d1080, d4333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8573 (p : Pattern) (guard : d4765 p = 1) : d1081 p ≤ (4 : Int) + d4334 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1081, d4334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8571 p hg
    simpa only [d1081, d4334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1081, d4334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8572 p hg
    simpa only [d1081, d4334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8574 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d124 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8575 (p : Pattern) (guard : d4765 p = 1) : d1082 p ≤ (4 : Int) + d4335 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1082, d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8511 p hg
    simpa only [d4765, d1082, d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1082, d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8574 p hg
    simpa only [d4765, d1082, d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8576 (p : Pattern) (guard : d4765 p = 1) : d1083 p ≤ (4 : Int) + d4337 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1083, d4337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8575 p hg
    simpa only [d1083, d4337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1083, d4337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8515 p hg
    simpa only [d1083, d4337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8577 (p : Pattern) (guard : d4765 p = 1) : d1084 p ≤ (4 : Int) + d4338 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1084, d4338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8573 p hg
    simpa only [d1084, d4338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1084, d4338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8576 p hg
    simpa only [d1084, d4338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8578 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (4 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8579 (p : Pattern) (guard : d4765 p = 1) : d1085 p ≤ (4 : Int) + d4339 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1085, d4339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8518 p hg
    simpa only [d4765, d1085, d4339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1085, d4339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8578 p hg
    simpa only [d4765, d1085, d4339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8580 (p : Pattern) (guard : d4765 p = 1) : d1086 p ≤ (4 : Int) + d4340 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1086, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8579 p hg
    simpa only [d1086, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1086, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8527 p hg
    simpa only [d1086, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8581 (p : Pattern) (guard : d4765 p = 1) : d1087 p ≤ (4 : Int) + d4344 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1087, d4344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8580 p hg
    simpa only [d1087, d4344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1087, d4344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8535 p hg
    simpa only [d1087, d4344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8582 (p : Pattern) (guard : d4765 p = 1) : d1088 p ≤ (4 : Int) + d4345 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1088, d4345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8577 p hg
    simpa only [d1088, d4345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1088, d4345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8581 p hg
    simpa only [d1088, d4345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8583 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8584 (p : Pattern) (guard : d4765 p = 1) : d1089 p ≤ (4 : Int) + d105 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3960 p hg
    simpa only [d4765, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8583 p hg
    simpa only [d4765, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8585 (p : Pattern) (guard : d4765 p = 1) : d1090 p ≤ (4 : Int) + d4334 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1090, d4334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8584 p hg
    simpa only [d1090, d4334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1090, d4334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8541 p hg
    simpa only [d1090, d4334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8586 (p : Pattern) (guard : d4765 p = 1) : d1091 p ≤ (4 : Int) + d4346 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1091, d4346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8585 p hg
    simpa only [d1091, d4346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1091, d4346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8543 p hg
    simpa only [d1091, d4346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8587 (p : Pattern) (guard : d4765 p = 1) : d1092 p ≤ (4 : Int) + d4348 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1092, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8586 p hg
    simpa only [d1092, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1092, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8552 p hg
    simpa only [d1092, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8588 (p : Pattern) (guard : d4765 p = 1) : d1093 p ≤ (4 : Int) + d4349 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1093, d4349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8582 p hg
    simpa only [d1093, d4349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1093, d4349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8587 p hg
    simpa only [d1093, d4349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8589 (p : Pattern) (guard : d4765 p = 1) : d1094 p ≤ (4 : Int) + d4356 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1094, d4356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8587 p hg
    simpa only [d1094, d4356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1094, d4356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8408 p hg
    simpa only [d1094, d4356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8590 (p : Pattern) (guard : d4765 p = 1) : d1095 p ≤ (4 : Int) + d4357 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1095, d4357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8588 p hg
    simpa only [d1095, d4357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1095, d4357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8589 p hg
    simpa only [d1095, d4357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8591 (p : Pattern) (guard : d4765 p = 1) : d1096 p ≤ (4 : Int) + d4358 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1096, d4358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8569 p hg
    simpa only [d1096, d4358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1096, d4358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8590 p hg
    simpa only [d1096, d4358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8592 (p : Pattern) (guard : d4765 p = 1) : d1097 p ≤ (4 : Int) + d4359 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1097, d4359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8471 p hg
    simpa only [d1097, d4359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1097, d4359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8591 p hg
    simpa only [d1097, d4359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8593 (p : Pattern) (guard : d4765 p = 1) : d1098 p ≤ (4 : Int) + d4360 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1098, d4360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8503 p hg
    simpa only [d1098, d4360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1098, d4360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8592 p hg
    simpa only [d1098, d4360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8594 (p : Pattern) (guard : d4765 p = 1) : d968 p ≤ (4 : Int) + d53 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8405 p hg
    simpa only [d4765, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8458 p hg
    simpa only [d4765, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8595 (p : Pattern) (guard : d4765 p = 1) : d1099 p ≤ (4 : Int) + d4361 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1099, d4361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8594 p hg
    simpa only [d1099, d4361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1099, d4361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8415 p hg
    simpa only [d1099, d4361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8596 (p : Pattern) (guard : d4765 p = 1) : d1101 p ≤ (4 : Int) + d1101 p := by
  omega
theorem compare8597 (p : Pattern) (guard : d4765 p = 1) : d1102 p ≤ (4 : Int) + d4362 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1102, d4362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8595 p hg
    simpa only [d1102, d4362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1102, d4362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8596 p hg
    simpa only [d1102, d4362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8598 (p : Pattern) (guard : d4765 p = 1) : d1103 p ≤ (4 : Int) + d4363 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1103, d4363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8457 p hg
    simpa only [d1103, d4363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1103, d4363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8597 p hg
    simpa only [d1103, d4363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8599 (p : Pattern) (guard : d4765 p = 1) : d1104 p ≤ (4 : Int) + d4364 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1104, d4364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8498 p hg
    simpa only [d1104, d4364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1104, d4364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8598 p hg
    simpa only [d1104, d4364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8600 (p : Pattern) (guard : d4765 p = 1) : d1105 p ≤ (4 : Int) + d4365 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1105, d4365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8598 p hg
    simpa only [d1105, d4365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1105, d4365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8408 p hg
    simpa only [d1105, d4365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8601 (p : Pattern) (guard : d4765 p = 1) : d1106 p ≤ (4 : Int) + d4366 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1106, d4366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8599 p hg
    simpa only [d1106, d4366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1106, d4366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8600 p hg
    simpa only [d1106, d4366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8602 (p : Pattern) (guard : d4765 p = 1) : d1107 p ≤ (4 : Int) + d4367 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1107, d4367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8493 p hg
    simpa only [d1107, d4367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1107, d4367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8601 p hg
    simpa only [d1107, d4367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8603 (p : Pattern) (guard : d4765 p = 1) : d1108 p ≤ (4 : Int) + d4368 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1108, d4368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8471 p hg
    simpa only [d1108, d4368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1108, d4368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8602 p hg
    simpa only [d1108, d4368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8604 (p : Pattern) (guard : d0 p = 1) : d448 p ≤ (4 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8605 (p : Pattern) (guard : d4765 p = 1) : d1109 p ≤ (4 : Int) + d4339 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1109, d4339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8518 p hg
    simpa only [d4765, d1109, d4339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1109, d4339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8604 p hg
    simpa only [d4765, d1109, d4339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8606 (p : Pattern) (guard : d4765 p = 1) : d1110 p ≤ (4 : Int) + d4340 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1110, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8605 p hg
    simpa only [d1110, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1110, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8527 p hg
    simpa only [d1110, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8607 (p : Pattern) (guard : d4765 p = 1) : d1111 p ≤ (4 : Int) + d4344 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1111, d4344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8606 p hg
    simpa only [d1111, d4344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1111, d4344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8535 p hg
    simpa only [d1111, d4344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8608 (p : Pattern) (guard : d4765 p = 1) : d1112 p ≤ (4 : Int) + d4345 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1112, d4345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8517 p hg
    simpa only [d1112, d4345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1112, d4345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8607 p hg
    simpa only [d1112, d4345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8609 (p : Pattern) (guard : d4765 p = 1) : d1113 p ≤ (4 : Int) + d4349 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1113, d4349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8608 p hg
    simpa only [d1113, d4349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1113, d4349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8553 p hg
    simpa only [d1113, d4349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8610 (p : Pattern) (guard : d4765 p = 1) : d1114 p ≤ (4 : Int) + d4348 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1114, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8558 p hg
    simpa only [d1114, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1114, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8552 p hg
    simpa only [d1114, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8611 (p : Pattern) (guard : d4765 p = 1) : d1115 p ≤ (4 : Int) + d4354 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1115, d4354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8610 p hg
    simpa only [d1115, d4354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1115, d4354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8567 p hg
    simpa only [d1115, d4354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8612 (p : Pattern) (guard : d4765 p = 1) : d1116 p ≤ (4 : Int) + d4355 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1116, d4355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8609 p hg
    simpa only [d1116, d4355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1116, d4355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8611 p hg
    simpa only [d1116, d4355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8613 (p : Pattern) (guard : d0 p = 1) : d450 p ≤ (4 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8614 (p : Pattern) (guard : d4765 p = 1) : d1117 p ≤ (4 : Int) + d105 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3960 p hg
    simpa only [d4765, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8613 p hg
    simpa only [d4765, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8615 (p : Pattern) (guard : d4765 p = 1) : d1118 p ≤ (4 : Int) + d4333 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1118, d4333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4046 p hg
    simpa only [d4765, d1118, d4333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1118, d4333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8540 p hg
    simpa only [d4765, d1118, d4333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8616 (p : Pattern) (guard : d4765 p = 1) : d1119 p ≤ (4 : Int) + d4334 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1119, d4334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8614 p hg
    simpa only [d1119, d4334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1119, d4334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8615 p hg
    simpa only [d1119, d4334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8617 (p : Pattern) (guard : d4147 p = 1) : d269 p ≤ (4 : Int) + d269 p := by
  omega
theorem compare8618 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d272 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8619 (p : Pattern) (guard : d4765 p = 1) : d1120 p ≤ (4 : Int) + d4369 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1120, d4369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8617 p hg
    simpa only [d4765, d1120, d4369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1120, d4369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8618 p hg
    simpa only [d4765, d1120, d4369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8620 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d277 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8621 (p : Pattern) (guard : d4765 p = 1) : d1121 p ≤ (4 : Int) + d4370 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1121, d4370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4035 p hg
    simpa only [d4765, d1121, d4370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1121, d4370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8620 p hg
    simpa only [d4765, d1121, d4370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8622 (p : Pattern) (guard : d4765 p = 1) : d1122 p ≤ (4 : Int) + d4371 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1122, d4371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8619 p hg
    simpa only [d1122, d4371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1122, d4371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8621 p hg
    simpa only [d1122, d4371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8623 (p : Pattern) (guard : d4765 p = 1) : d1123 p ≤ (4 : Int) + d4372 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1123, d4372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8616 p hg
    simpa only [d1123, d4372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1123, d4372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8622 p hg
    simpa only [d1123, d4372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8624 (p : Pattern) (guard : d1 p = 1) : d282 p ≤ (4 : Int) + d116 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2619 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8523 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8625 (p : Pattern) (guard : d1 p = 1) : d298 p ≤ (4 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d298, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8624 p hg
    simpa only [d298, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d298, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8524 p hg
    simpa only [d298, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8626 (p : Pattern) (guard : d4147 p = 1) : d925 p ≤ (4 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3982 p hg
    simpa only [d4147, d925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8625 p hg
    simpa only [d4147, d925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8627 (p : Pattern) (guard : d4765 p = 1) : d1124 p ≤ (4 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1124, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8626 p hg
    simpa only [d4765, d1124, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1124, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d4765, d1124, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8628 (p : Pattern) (guard : d4765 p = 1) : d1125 p ≤ (4 : Int) + d4340 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1125, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8546 p hg
    simpa only [d1125, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1125, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8627 p hg
    simpa only [d1125, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8629 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d283 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8630 (p : Pattern) (guard : d4765 p = 1) : d1124 p ≤ (4 : Int) + d4373 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1124, d4373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8626 p hg
    simpa only [d4765, d1124, d4373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1124, d4373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8629 p hg
    simpa only [d4765, d1124, d4373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8631 (p : Pattern) (guard : d0 p = 1) : d283 p ≤ (4 : Int) + d283 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8632 (p : Pattern) (guard : d1 p = 1) : d1126 p ≤ (4 : Int) + d282 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1126, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2596 p hg
    simpa only [d1126, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1126, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2609 p hg
    simpa only [d1126, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8633 (p : Pattern) (guard : d1 p = 1) : d1127 p ≤ (4 : Int) + d283 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1127, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8632 p hg
    simpa only [d1127, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1127, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d1127, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8634 (p : Pattern) (guard : d4147 p = 1) : d1128 p ≤ (4 : Int) + d283 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8631 p hg
    simpa only [d4147, d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8633 p hg
    simpa only [d4147, d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8635 (p : Pattern) (guard : d4765 p = 1) : d1129 p ≤ (4 : Int) + d4374 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1129, d4374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8634 p hg
    simpa only [d4765, d1129, d4374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1129, d4374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d4765, d1129, d4374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8636 (p : Pattern) (guard : d4765 p = 1) : d1130 p ≤ (4 : Int) + d4375 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1130, d4375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8630 p hg
    simpa only [d1130, d4375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1130, d4375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8635 p hg
    simpa only [d1130, d4375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8637 (p : Pattern) (guard : d4765 p = 1) : d1131 p ≤ (4 : Int) + d4376 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1131, d4376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8628 p hg
    simpa only [d1131, d4376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1131, d4376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8636 p hg
    simpa only [d1131, d4376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8638 (p : Pattern) (guard : d4765 p = 1) : d1132 p ≤ (4 : Int) + d4377 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1132, d4377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8623 p hg
    simpa only [d1132, d4377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1132, d4377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8637 p hg
    simpa only [d1132, d4377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8639 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d269 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8640 (p : Pattern) (guard : d4765 p = 1) : d1089 p ≤ (4 : Int) + d4378 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1089, d4378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3960 p hg
    simpa only [d4765, d1089, d4378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1089, d4378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8639 p hg
    simpa only [d4765, d1089, d4378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8641 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (4 : Int) + d268 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2718 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2619 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8642 (p : Pattern) (guard : d1 p = 1) : d117 p ≤ (4 : Int) + d117 p := by
  omega
theorem compare8643 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (4 : Int) + d269 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8641 p hg
    simpa only [d132, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8642 p hg
    simpa only [d132, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8644 (p : Pattern) (guard : d4147 p = 1) : d1133 p ≤ (4 : Int) + d269 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4030 p hg
    simpa only [d4147, d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8643 p hg
    simpa only [d4147, d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8645 (p : Pattern) (guard : d4765 p = 1) : d1134 p ≤ (4 : Int) + d4379 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1134, d4379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8644 p hg
    simpa only [d4765, d1134, d4379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1134, d4379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8620 p hg
    simpa only [d4765, d1134, d4379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8646 (p : Pattern) (guard : d4765 p = 1) : d1135 p ≤ (4 : Int) + d4380 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1135, d4380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8640 p hg
    simpa only [d1135, d4380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1135, d4380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8645 p hg
    simpa only [d1135, d4380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8647 (p : Pattern) (guard : d4765 p = 1) : d1136 p ≤ (4 : Int) + d4381 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1136, d4381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8646 p hg
    simpa only [d1136, d4381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1136, d4381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8543 p hg
    simpa only [d1136, d4381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8648 (p : Pattern) (guard : d4147 p = 1) : d132 p ≤ (4 : Int) + d132 p := by
  omega
theorem compare8649 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d298 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8650 (p : Pattern) (guard : d4765 p = 1) : d1061 p ≤ (4 : Int) + d4382 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1061, d4382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8648 p hg
    simpa only [d4765, d1061, d4382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1061, d4382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8649 p hg
    simpa only [d4765, d1061, d4382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8651 (p : Pattern) (guard : d0 p = 1) : d298 p ≤ (4 : Int) + d298 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8652 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (4 : Int) + d282 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8523 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2606 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8653 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (4 : Int) + d108 p := by
  omega
theorem compare8654 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (4 : Int) + d298 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8652 p hg
    simpa only [d109, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8653 p hg
    simpa only [d109, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8655 (p : Pattern) (guard : d4147 p = 1) : d1137 p ≤ (4 : Int) + d298 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8651 p hg
    simpa only [d4147, d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8654 p hg
    simpa only [d4147, d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8656 (p : Pattern) (guard : d4765 p = 1) : d1138 p ≤ (4 : Int) + d4383 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1138, d4383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8655 p hg
    simpa only [d4765, d1138, d4383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1138, d4383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d4765, d1138, d4383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8657 (p : Pattern) (guard : d4765 p = 1) : d1139 p ≤ (4 : Int) + d4384 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1139, d4384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8650 p hg
    simpa only [d1139, d4384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1139, d4384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8656 p hg
    simpa only [d1139, d4384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8658 (p : Pattern) (guard : d4765 p = 1) : d1141 p ≤ (4 : Int) + d1141 p := by
  omega
theorem compare8659 (p : Pattern) (guard : d4765 p = 1) : d1142 p ≤ (4 : Int) + d4385 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1142, d4385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8657 p hg
    simpa only [d1142, d4385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1142, d4385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8658 p hg
    simpa only [d1142, d4385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8660 (p : Pattern) (guard : d4765 p = 1) : d1143 p ≤ (4 : Int) + d4386 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1143, d4386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8647 p hg
    simpa only [d1143, d4386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1143, d4386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8659 p hg
    simpa only [d1143, d4386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8661 (p : Pattern) (guard : d4765 p = 1) : d1144 p ≤ (4 : Int) + d4387 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1144, d4387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8638 p hg
    simpa only [d1144, d4387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1144, d4387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8660 p hg
    simpa only [d1144, d4387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8662 (p : Pattern) (guard : d4765 p = 1) : d1145 p ≤ (4 : Int) + d4388 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1145, d4388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8660 p hg
    simpa only [d1145, d4388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1145, d4388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8408 p hg
    simpa only [d1145, d4388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8663 (p : Pattern) (guard : d4765 p = 1) : d1146 p ≤ (4 : Int) + d4389 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1146, d4389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8661 p hg
    simpa only [d1146, d4389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1146, d4389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8662 p hg
    simpa only [d1146, d4389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8664 (p : Pattern) (guard : d4765 p = 1) : d1147 p ≤ (4 : Int) + d4390 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1147, d4390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8612 p hg
    simpa only [d1147, d4390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1147, d4390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8663 p hg
    simpa only [d1147, d4390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8665 (p : Pattern) (guard : d4765 p = 1) : d1148 p ≤ (4 : Int) + d4391 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1148, d4391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8471 p hg
    simpa only [d1148, d4391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1148, d4391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8664 p hg
    simpa only [d1148, d4391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8666 (p : Pattern) (guard : d4765 p = 1) : d1149 p ≤ (4 : Int) + d4392 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1149, d4392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8603 p hg
    simpa only [d1149, d4392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1149, d4392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8665 p hg
    simpa only [d1149, d4392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8667 (p : Pattern) (guard : d4765 p = 1) : d1150 p ≤ (4 : Int) + d4393 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1150, d4393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8593 p hg
    simpa only [d1150, d4393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1150, d4393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8666 p hg
    simpa only [d1150, d4393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8668 (p : Pattern) (guard : d0 p = 1) : d951 p ≤ (0 : Int) + d362 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8669 (p : Pattern) (guard : d4670 p = 1) : d952 p ≤ (0 : Int) + d790 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d952, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7785 p hg
    simpa only [d4670, d952, d790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d952, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8668 p hg
    simpa only [d4670, d952, d790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8670 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (0 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8671 (p : Pattern) (guard : d4395 p = 1) : d953 p ≤ (0 : Int) + d791 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d953, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4395, d953, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d953, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8670 p hg
    simpa only [d4395, d953, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8672 (p : Pattern) (guard : d0 p = 1) : d954 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8673 (p : Pattern) (guard : d4670 p = 1) : d955 p ≤ (0 : Int) + d792 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d955, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8671 p hg
    simpa only [d4670, d955, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d955, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8672 p hg
    simpa only [d4670, d955, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8674 (p : Pattern) (guard : d4670 p = 1) : d956 p ≤ (0 : Int) + d793 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d956, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8669 p hg
    simpa only [d956, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d956, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8673 p hg
    simpa only [d956, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8675 (p : Pattern) (guard : d0 p = 1) : d369 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8676 (p : Pattern) (guard : d4395 p = 1) : d957 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d957, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d957, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d957, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8675 p hg
    simpa only [d4395, d957, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8677 (p : Pattern) (guard : d0 p = 1) : d958 p ≤ (0 : Int) + d387 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8678 (p : Pattern) (guard : d4670 p = 1) : d959 p ≤ (0 : Int) + d794 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d959, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8676 p hg
    simpa only [d4670, d959, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d959, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8677 p hg
    simpa only [d4670, d959, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8679 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d798 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
