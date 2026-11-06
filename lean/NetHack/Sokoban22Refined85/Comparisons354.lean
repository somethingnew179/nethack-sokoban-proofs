/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons353
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare49560 (p : Pattern) (guard : d8130 p = 1) : d1005 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1005, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49559 p hg
    simpa only [d8130, d1005, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1005, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47871 p hg
    simpa only [d8130, d1005, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49561 (p : Pattern) (guard : d8131 p = 1) : d1011 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1011, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49557 p hg
    simpa only [d8131, d1011, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1011, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49560 p hg
    simpa only [d8131, d1011, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49562 (p : Pattern) (guard : d8137 p = 1) : d1012 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1012, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49561 p hg
    simpa only [d8137, d1012, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1012, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d1012, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49563 (p : Pattern) (guard : d8138 p = 1) : d1013 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1013, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49554 p hg
    simpa only [d8138, d1013, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1013, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49562 p hg
    simpa only [d8138, d1013, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49564 (p : Pattern) (guard : d8139 p = 1) : d1014 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d1014, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49540 p hg
    simpa only [d8139, d1014, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d1014, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49563 p hg
    simpa only [d8139, d1014, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49565 (p : Pattern) (guard : d8107 p = 1) : d355 p ≤ (0 : Int) + d355 p := by
  omega
theorem compare49566 (p : Pattern) (guard : d8108 p = 1) : d1042 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1042, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35120 p hg
    simpa only [d8108, d1042, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1042, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49565 p hg
    simpa only [d8108, d1042, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49567 (p : Pattern) (guard : d8113 p = 1) : d1044 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1044, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47946 p hg
    simpa only [d8113, d1044, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1044, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49480 p hg
    simpa only [d8113, d1044, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49568 (p : Pattern) (guard : d8114 p = 1) : d1045 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1045, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49566 p hg
    simpa only [d8114, d1045, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1045, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49567 p hg
    simpa only [d8114, d1045, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49569 (p : Pattern) (guard : d8113 p = 1) : d1046 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1046, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47949 p hg
    simpa only [d8113, d1046, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1046, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d8113, d1046, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49570 (p : Pattern) (guard : d8118 p = 1) : d1047 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35195 p hg
    simpa only [d8118, d1047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49571 (p : Pattern) (guard : d8119 p = 1) : d1048 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1048, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49569 p hg
    simpa only [d8119, d1048, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1048, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49570 p hg
    simpa only [d8119, d1048, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49572 (p : Pattern) (guard : d8120 p = 1) : d1049 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1049, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49568 p hg
    simpa only [d8120, d1049, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1049, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49571 p hg
    simpa only [d8120, d1049, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49573 (p : Pattern) (guard : d8112 p = 1) : d386 p ≤ (0 : Int) + d386 p := by
  omega
theorem compare49574 (p : Pattern) (guard : d8113 p = 1) : d1050 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1050, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35216 p hg
    simpa only [d8113, d1050, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1050, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49573 p hg
    simpa only [d8113, d1050, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49575 (p : Pattern) (guard : d8119 p = 1) : d1052 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1052, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49574 p hg
    simpa only [d8119, d1052, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1052, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47971 p hg
    simpa only [d8119, d1052, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49576 (p : Pattern) (guard : d8118 p = 1) : d1051 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1051, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47980 p hg
    simpa only [d8118, d1051, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1051, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1051, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49577 (p : Pattern) (guard : d8124 p = 1) : d1055 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1055, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49576 p hg
    simpa only [d8124, d1055, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1055, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43999 p hg
    simpa only [d8124, d1055, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49578 (p : Pattern) (guard : d8125 p = 1) : d1056 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1056, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49575 p hg
    simpa only [d8125, d1056, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1056, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49577 p hg
    simpa only [d8125, d1056, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49579 (p : Pattern) (guard : d8126 p = 1) : d1057 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1057, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49572 p hg
    simpa only [d8126, d1057, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1057, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49578 p hg
    simpa only [d8126, d1057, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49580 (p : Pattern) (guard : d8113 p = 1) : d1058 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1058, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35254 p hg
    simpa only [d8113, d1058, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1058, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49480 p hg
    simpa only [d8113, d1058, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49581 (p : Pattern) (guard : d8118 p = 1) : d1059 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1059, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47986 p hg
    simpa only [d8118, d1059, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1059, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1059, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49582 (p : Pattern) (guard : d8119 p = 1) : d1060 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1060, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49580 p hg
    simpa only [d8119, d1060, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1060, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49581 p hg
    simpa only [d8119, d1060, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49583 (p : Pattern) (guard : d8125 p = 1) : d1063 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1063, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49582 p hg
    simpa only [d8125, d1063, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1063, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47991 p hg
    simpa only [d8125, d1063, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49584 (p : Pattern) (guard : d8118 p = 1) : d1059 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1059, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35284 p hg
    simpa only [d8118, d1059, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1059, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1059, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49585 (p : Pattern) (guard : d8124 p = 1) : d1065 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1065, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49584 p hg
    simpa only [d8124, d1065, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1065, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47996 p hg
    simpa only [d8124, d1065, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49586 (p : Pattern) (guard : d8130 p = 1) : d1067 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1067, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49585 p hg
    simpa only [d8130, d1067, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1067, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47998 p hg
    simpa only [d8130, d1067, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49587 (p : Pattern) (guard : d8131 p = 1) : d1068 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1068, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49583 p hg
    simpa only [d8131, d1068, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1068, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49586 p hg
    simpa only [d8131, d1068, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49588 (p : Pattern) (guard : d8132 p = 1) : d1069 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1069, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49579 p hg
    simpa only [d8132, d1069, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1069, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49587 p hg
    simpa only [d8132, d1069, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49589 (p : Pattern) (guard : d8113 p = 1) : d1070 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1070, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38201 p hg
    simpa only [d8113, d1070, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1070, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49547 p hg
    simpa only [d8113, d1070, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49590 (p : Pattern) (guard : d8118 p = 1) : d1059 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1059, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48002 p hg
    simpa only [d8118, d1059, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1059, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1059, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49591 (p : Pattern) (guard : d8119 p = 1) : d1071 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1071, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49589 p hg
    simpa only [d8119, d1071, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1071, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49590 p hg
    simpa only [d8119, d1071, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49592 (p : Pattern) (guard : d8125 p = 1) : d1072 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1072, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49591 p hg
    simpa only [d8125, d1072, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1072, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48007 p hg
    simpa only [d8125, d1072, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49593 (p : Pattern) (guard : d8117 p = 1) : d374 p ≤ (0 : Int) + d374 p := by
  omega
theorem compare49594 (p : Pattern) (guard : d8118 p = 1) : d1073 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1073, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41426 p hg
    simpa only [d8118, d1073, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1073, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49593 p hg
    simpa only [d8118, d1073, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49595 (p : Pattern) (guard : d8124 p = 1) : d1074 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1074, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49594 p hg
    simpa only [d8124, d1074, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1074, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47996 p hg
    simpa only [d8124, d1074, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49596 (p : Pattern) (guard : d8130 p = 1) : d1075 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1075, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49595 p hg
    simpa only [d8130, d1075, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1075, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47998 p hg
    simpa only [d8130, d1075, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49597 (p : Pattern) (guard : d8131 p = 1) : d1076 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1076, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49592 p hg
    simpa only [d8131, d1076, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1076, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49596 p hg
    simpa only [d8131, d1076, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49598 (p : Pattern) (guard : d8137 p = 1) : d1077 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1077, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49597 p hg
    simpa only [d8137, d1077, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1077, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38220 p hg
    simpa only [d8137, d1077, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49599 (p : Pattern) (guard : d8138 p = 1) : d1078 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1078, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49588 p hg
    simpa only [d8138, d1078, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1078, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49598 p hg
    simpa only [d8138, d1078, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49600 (p : Pattern) (guard : d8112 p = 1) : d389 p ≤ (0 : Int) + d389 p := by
  omega
theorem compare49601 (p : Pattern) (guard : d8113 p = 1) : d1079 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1079, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35303 p hg
    simpa only [d8113, d1079, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1079, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49600 p hg
    simpa only [d8113, d1079, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49602 (p : Pattern) (guard : d8118 p = 1) : d1080 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1080, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48017 p hg
    simpa only [d8118, d1080, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1080, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1080, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49603 (p : Pattern) (guard : d8119 p = 1) : d1081 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1081, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49601 p hg
    simpa only [d8119, d1081, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1081, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49602 p hg
    simpa only [d8119, d1081, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49604 (p : Pattern) (guard : d8118 p = 1) : d1082 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1082, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48020 p hg
    simpa only [d8118, d1082, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1082, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1082, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49605 (p : Pattern) (guard : d8123 p = 1) : d1047 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35320 p hg
    simpa only [d8123, d1047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49606 (p : Pattern) (guard : d8124 p = 1) : d1083 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1083, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49604 p hg
    simpa only [d8124, d1083, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1083, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49605 p hg
    simpa only [d8124, d1083, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49607 (p : Pattern) (guard : d8125 p = 1) : d1084 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1084, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49603 p hg
    simpa only [d8125, d1084, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1084, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49606 p hg
    simpa only [d8125, d1084, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49608 (p : Pattern) (guard : d8117 p = 1) : d371 p ≤ (0 : Int) + d371 p := by
  omega
theorem compare49609 (p : Pattern) (guard : d8118 p = 1) : d1085 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1085, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35336 p hg
    simpa only [d8118, d1085, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1085, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49608 p hg
    simpa only [d8118, d1085, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49610 (p : Pattern) (guard : d8124 p = 1) : d1086 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1086, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49609 p hg
    simpa only [d8124, d1086, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1086, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48027 p hg
    simpa only [d8124, d1086, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49611 (p : Pattern) (guard : d8123 p = 1) : d1051 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48029 p hg
    simpa only [d8123, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49612 (p : Pattern) (guard : d8129 p = 1) : d1055 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49611 p hg
    simpa only [d8129, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8786 p hg
    simpa only [d8129, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49613 (p : Pattern) (guard : d8130 p = 1) : d1087 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1087, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49610 p hg
    simpa only [d8130, d1087, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1087, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49612 p hg
    simpa only [d8130, d1087, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49614 (p : Pattern) (guard : d8131 p = 1) : d1088 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1088, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49607 p hg
    simpa only [d8131, d1088, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1088, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49613 p hg
    simpa only [d8131, d1088, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49615 (p : Pattern) (guard : d8118 p = 1) : d1089 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1089, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35355 p hg
    simpa only [d8118, d1089, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1089, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1089, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49616 (p : Pattern) (guard : d8123 p = 1) : d1059 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48034 p hg
    simpa only [d8123, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49617 (p : Pattern) (guard : d8124 p = 1) : d1090 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1090, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49615 p hg
    simpa only [d8124, d1090, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1090, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49616 p hg
    simpa only [d8124, d1090, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49618 (p : Pattern) (guard : d8130 p = 1) : d1091 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1091, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49617 p hg
    simpa only [d8130, d1091, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1091, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48039 p hg
    simpa only [d8130, d1091, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49619 (p : Pattern) (guard : d8123 p = 1) : d1059 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1059, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35371 p hg
    simpa only [d8123, d1059, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1059, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1059, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49620 (p : Pattern) (guard : d8129 p = 1) : d1065 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1065, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49619 p hg
    simpa only [d8129, d1065, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1065, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8798 p hg
    simpa only [d8129, d1065, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49621 (p : Pattern) (guard : d8135 p = 1) : d1067 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1067, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49620 p hg
    simpa only [d8135, d1067, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1067, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48043 p hg
    simpa only [d8135, d1067, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49622 (p : Pattern) (guard : d8136 p = 1) : d1092 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1092, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49618 p hg
    simpa only [d8136, d1092, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1092, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49621 p hg
    simpa only [d8136, d1092, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49623 (p : Pattern) (guard : d8137 p = 1) : d1093 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1093, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49614 p hg
    simpa only [d8137, d1093, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1093, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49622 p hg
    simpa only [d8137, d1093, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49624 (p : Pattern) (guard : d8118 p = 1) : d1089 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1089, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38228 p hg
    simpa only [d8118, d1089, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1089, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1089, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49625 (p : Pattern) (guard : d8124 p = 1) : d1090 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1090, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49624 p hg
    simpa only [d8124, d1090, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1090, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49616 p hg
    simpa only [d8124, d1090, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49626 (p : Pattern) (guard : d8130 p = 1) : d1091 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1091, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49625 p hg
    simpa only [d8130, d1091, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1091, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48039 p hg
    simpa only [d8130, d1091, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49627 (p : Pattern) (guard : d8123 p = 1) : d1059 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1059, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41434 p hg
    simpa only [d8123, d1059, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1059, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1059, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49628 (p : Pattern) (guard : d8129 p = 1) : d1065 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1065, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49627 p hg
    simpa only [d8129, d1065, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1065, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8798 p hg
    simpa only [d8129, d1065, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49629 (p : Pattern) (guard : d8135 p = 1) : d1067 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1067, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49628 p hg
    simpa only [d8135, d1067, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1067, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48043 p hg
    simpa only [d8135, d1067, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49630 (p : Pattern) (guard : d8136 p = 1) : d1092 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1092, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49626 p hg
    simpa only [d8136, d1092, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1092, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49629 p hg
    simpa only [d8136, d1092, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49631 (p : Pattern) (guard : d8142 p = 1) : d1094 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1094, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49630 p hg
    simpa only [d8142, d1094, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1094, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d1094, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49632 (p : Pattern) (guard : d8143 p = 1) : d1095 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1095, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49623 p hg
    simpa only [d8143, d1095, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1095, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49631 p hg
    simpa only [d8143, d1095, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49633 (p : Pattern) (guard : d8144 p = 1) : d1096 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d1096, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49599 p hg
    simpa only [d8144, d1096, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d1096, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49632 p hg
    simpa only [d8144, d1096, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49634 (p : Pattern) (guard : d8145 p = 1) : d1097 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d1097, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49564 p hg
    simpa only [d8145, d1097, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d1097, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49633 p hg
    simpa only [d8145, d1097, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49635 (p : Pattern) (guard : d8146 p = 1) : d1098 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49510 p hg
    simpa only [d8146, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49634 p hg
    simpa only [d8146, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49636 (p : Pattern) (guard : d8108 p = 1) : d1015 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1015, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35391 p hg
    simpa only [d8108, d1015, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1015, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49565 p hg
    simpa only [d8108, d1015, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49637 (p : Pattern) (guard : d8113 p = 1) : d1016 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1016, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48058 p hg
    simpa only [d8113, d1016, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1016, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49480 p hg
    simpa only [d8113, d1016, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49638 (p : Pattern) (guard : d8114 p = 1) : d1017 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1017, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49636 p hg
    simpa only [d8114, d1017, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1017, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49637 p hg
    simpa only [d8114, d1017, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49639 (p : Pattern) (guard : d8113 p = 1) : d1018 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1018, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d8113, d1018, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1018, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d8113, d1018, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49640 (p : Pattern) (guard : d8119 p = 1) : d1019 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1019, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49639 p hg
    simpa only [d8119, d1019, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1019, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49477 p hg
    simpa only [d8119, d1019, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49641 (p : Pattern) (guard : d8120 p = 1) : d1020 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1020, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49638 p hg
    simpa only [d8120, d1020, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1020, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49640 p hg
    simpa only [d8120, d1020, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49642 (p : Pattern) (guard : d8113 p = 1) : d1021 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1021, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35421 p hg
    simpa only [d8113, d1021, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1021, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49573 p hg
    simpa only [d8113, d1021, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49643 (p : Pattern) (guard : d8118 p = 1) : d960 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d960, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48073 p hg
    simpa only [d8118, d960, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d960, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d960, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49644 (p : Pattern) (guard : d8119 p = 1) : d1022 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1022, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49642 p hg
    simpa only [d8119, d1022, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1022, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49643 p hg
    simpa only [d8119, d1022, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49645 (p : Pattern) (guard : d8118 p = 1) : d960 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d960, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48076 p hg
    simpa only [d8118, d960, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d960, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d960, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49646 (p : Pattern) (guard : d8124 p = 1) : d962 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d962, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49645 p hg
    simpa only [d8124, d962, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d962, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49485 p hg
    simpa only [d8124, d962, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49647 (p : Pattern) (guard : d8125 p = 1) : d1023 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1023, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49644 p hg
    simpa only [d8125, d1023, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1023, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49646 p hg
    simpa only [d8125, d1023, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49648 (p : Pattern) (guard : d8126 p = 1) : d1024 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1024, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49641 p hg
    simpa only [d8126, d1024, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1024, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49647 p hg
    simpa only [d8126, d1024, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49649 (p : Pattern) (guard : d8113 p = 1) : d1025 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1025, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35455 p hg
    simpa only [d8113, d1025, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1025, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49480 p hg
    simpa only [d8113, d1025, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49650 (p : Pattern) (guard : d8119 p = 1) : d1026 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1026, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49649 p hg
    simpa only [d8119, d1026, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1026, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49495 p hg
    simpa only [d8119, d1026, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49651 (p : Pattern) (guard : d8125 p = 1) : d1027 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1027, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49650 p hg
    simpa only [d8125, d1027, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1027, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49493 p hg
    simpa only [d8125, d1027, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49652 (p : Pattern) (guard : d8118 p = 1) : d966 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d966, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35473 p hg
    simpa only [d8118, d966, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d966, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d966, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49653 (p : Pattern) (guard : d8124 p = 1) : d1004 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1004, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49652 p hg
    simpa only [d8124, d1004, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1004, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47870 p hg
    simpa only [d8124, d1004, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49654 (p : Pattern) (guard : d8130 p = 1) : d1005 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1005, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49653 p hg
    simpa only [d8130, d1005, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1005, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47871 p hg
    simpa only [d8130, d1005, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49655 (p : Pattern) (guard : d8131 p = 1) : d1028 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1028, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49651 p hg
    simpa only [d8131, d1028, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1028, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49654 p hg
    simpa only [d8131, d1028, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49656 (p : Pattern) (guard : d8132 p = 1) : d1029 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1029, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49648 p hg
    simpa only [d8132, d1029, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1029, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49655 p hg
    simpa only [d8132, d1029, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49657 (p : Pattern) (guard : d8113 p = 1) : d965 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d965, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35616 p hg
    simpa only [d8113, d965, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d965, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49547 p hg
    simpa only [d8113, d965, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49658 (p : Pattern) (guard : d8119 p = 1) : d967 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d967, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49657 p hg
    simpa only [d8119, d967, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d967, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49503 p hg
    simpa only [d8119, d967, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49659 (p : Pattern) (guard : d8118 p = 1) : d968 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48091 p hg
    simpa only [d8118, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49660 (p : Pattern) (guard : d8124 p = 1) : d969 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d969, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49659 p hg
    simpa only [d8124, d969, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d969, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d969, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49661 (p : Pattern) (guard : d8125 p = 1) : d970 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d970, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49658 p hg
    simpa only [d8125, d970, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d970, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49660 p hg
    simpa only [d8125, d970, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49662 (p : Pattern) (guard : d8118 p = 1) : d971 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d971, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35630 p hg
    simpa only [d8118, d971, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d971, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49593 p hg
    simpa only [d8118, d971, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49663 (p : Pattern) (guard : d8124 p = 1) : d973 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d973, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49662 p hg
    simpa only [d8124, d973, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d973, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47870 p hg
    simpa only [d8124, d973, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49664 (p : Pattern) (guard : d8130 p = 1) : d975 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d975, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49663 p hg
    simpa only [d8130, d975, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d975, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47871 p hg
    simpa only [d8130, d975, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49665 (p : Pattern) (guard : d8131 p = 1) : d976 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d976, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49661 p hg
    simpa only [d8131, d976, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d976, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49664 p hg
    simpa only [d8131, d976, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49666 (p : Pattern) (guard : d8118 p = 1) : d985 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d985, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38243 p hg
    simpa only [d8118, d985, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d985, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d985, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49667 (p : Pattern) (guard : d8124 p = 1) : d986 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d986, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49666 p hg
    simpa only [d8124, d986, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d986, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38245 p hg
    simpa only [d8124, d986, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49668 (p : Pattern) (guard : d8130 p = 1) : d987 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d987, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49667 p hg
    simpa only [d8130, d987, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d987, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38247 p hg
    simpa only [d8130, d987, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49669 (p : Pattern) (guard : d8136 p = 1) : d988 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d988, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49668 p hg
    simpa only [d8136, d988, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d988, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41444 p hg
    simpa only [d8136, d988, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49670 (p : Pattern) (guard : d8137 p = 1) : d1030 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1030, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49665 p hg
    simpa only [d8137, d1030, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1030, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49669 p hg
    simpa only [d8137, d1030, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49671 (p : Pattern) (guard : d8138 p = 1) : d1031 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1031, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49656 p hg
    simpa only [d8138, d1031, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1031, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49670 p hg
    simpa only [d8138, d1031, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49672 (p : Pattern) (guard : d8113 p = 1) : d978 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d978, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35485 p hg
    simpa only [d8113, d978, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d978, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49600 p hg
    simpa only [d8113, d978, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49673 (p : Pattern) (guard : d8118 p = 1) : d992 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d992, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48103 p hg
    simpa only [d8118, d992, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d992, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d992, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49674 (p : Pattern) (guard : d8119 p = 1) : d1032 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1032, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49672 p hg
    simpa only [d8119, d1032, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1032, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49673 p hg
    simpa only [d8119, d1032, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49675 (p : Pattern) (guard : d8118 p = 1) : d994 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d994, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48106 p hg
    simpa only [d8118, d994, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d994, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d994, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49676 (p : Pattern) (guard : d8123 p = 1) : d954 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35505 p hg
    simpa only [d8123, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49677 (p : Pattern) (guard : d8124 p = 1) : d995 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d995, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49675 p hg
    simpa only [d8124, d995, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d995, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49676 p hg
    simpa only [d8124, d995, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49678 (p : Pattern) (guard : d8125 p = 1) : d1033 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1033, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49674 p hg
    simpa only [d8125, d1033, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1033, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49677 p hg
    simpa only [d8125, d1033, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49679 (p : Pattern) (guard : d8118 p = 1) : d981 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d981, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35520 p hg
    simpa only [d8118, d981, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d981, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49608 p hg
    simpa only [d8118, d981, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49680 (p : Pattern) (guard : d8123 p = 1) : d960 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d960, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48112 p hg
    simpa only [d8123, d960, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d960, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d960, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49681 (p : Pattern) (guard : d8124 p = 1) : d1034 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1034, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49679 p hg
    simpa only [d8124, d1034, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1034, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49680 p hg
    simpa only [d8124, d1034, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49682 (p : Pattern) (guard : d8123 p = 1) : d960 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48115 p hg
    simpa only [d8123, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49683 (p : Pattern) (guard : d8129 p = 1) : d962 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49682 p hg
    simpa only [d8129, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8681 p hg
    simpa only [d8129, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49684 (p : Pattern) (guard : d8130 p = 1) : d1035 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1035, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49681 p hg
    simpa only [d8130, d1035, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1035, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49683 p hg
    simpa only [d8130, d1035, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49685 (p : Pattern) (guard : d8131 p = 1) : d1036 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1036, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49678 p hg
    simpa only [d8131, d1036, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1036, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49684 p hg
    simpa only [d8131, d1036, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49686 (p : Pattern) (guard : d8118 p = 1) : d1001 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1001, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35540 p hg
    simpa only [d8118, d1001, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1001, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1001, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49687 (p : Pattern) (guard : d8123 p = 1) : d966 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48120 p hg
    simpa only [d8123, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49688 (p : Pattern) (guard : d8124 p = 1) : d1002 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1002, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49686 p hg
    simpa only [d8124, d1002, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1002, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49687 p hg
    simpa only [d8124, d1002, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49689 (p : Pattern) (guard : d8123 p = 1) : d968 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d8123, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49690 (p : Pattern) (guard : d8129 p = 1) : d969 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49689 p hg
    simpa only [d8129, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49691 (p : Pattern) (guard : d8130 p = 1) : d1003 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1003, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49688 p hg
    simpa only [d8130, d1003, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1003, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49690 p hg
    simpa only [d8130, d1003, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49692 (p : Pattern) (guard : d8123 p = 1) : d968 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41470 p hg
    simpa only [d8123, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49693 (p : Pattern) (guard : d8129 p = 1) : d1099 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1099, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49692 p hg
    simpa only [d8129, d1099, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1099, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8693 p hg
    simpa only [d8129, d1099, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49694 (p : Pattern) (guard : d8135 p = 1) : d1102 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1102, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49693 p hg
    simpa only [d8135, d1102, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1102, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48129 p hg
    simpa only [d8135, d1102, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49695 (p : Pattern) (guard : d8136 p = 1) : d1103 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1103, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49691 p hg
    simpa only [d8136, d1103, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1103, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49694 p hg
    simpa only [d8136, d1103, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49696 (p : Pattern) (guard : d8137 p = 1) : d1104 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1104, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49685 p hg
    simpa only [d8137, d1104, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1104, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49695 p hg
    simpa only [d8137, d1104, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49697 (p : Pattern) (guard : d8118 p = 1) : d1001 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1001, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35678 p hg
    simpa only [d8118, d1001, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1001, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1001, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49698 (p : Pattern) (guard : d8124 p = 1) : d1002 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1002, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49697 p hg
    simpa only [d8124, d1002, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1002, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49687 p hg
    simpa only [d8124, d1002, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49699 (p : Pattern) (guard : d8130 p = 1) : d1003 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1003, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49698 p hg
    simpa only [d8130, d1003, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1003, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49690 p hg
    simpa only [d8130, d1003, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
