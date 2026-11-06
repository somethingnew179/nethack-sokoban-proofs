/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons352
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare49420 (p : Pattern) (guard : d8126 p = 1) : d1006 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1006, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49416 p hg
    simpa only [d8126, d1006, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1006, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49419 p hg
    simpa only [d8126, d1006, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49421 (p : Pattern) (guard : d8127 p = 1) : d1007 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1007, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49410 p hg
    simpa only [d8127, d1007, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1007, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49420 p hg
    simpa only [d8127, d1007, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49422 (p : Pattern) (guard : d8108 p = 1) : d1008 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1008, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38132 p hg
    simpa only [d8108, d1008, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1008, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49356 p hg
    simpa only [d8108, d1008, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49423 (p : Pattern) (guard : d8114 p = 1) : d1009 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1009, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49422 p hg
    simpa only [d8114, d1009, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1009, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49412 p hg
    simpa only [d8114, d1009, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49424 (p : Pattern) (guard : d8120 p = 1) : d1010 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1010, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49423 p hg
    simpa only [d8120, d1010, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1010, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49415 p hg
    simpa only [d8120, d1010, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49425 (p : Pattern) (guard : d8113 p = 1) : d966 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41392 p hg
    simpa only [d8113, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49426 (p : Pattern) (guard : d8119 p = 1) : d1004 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1004, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49425 p hg
    simpa only [d8119, d1004, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1004, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47779 p hg
    simpa only [d8119, d1004, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49427 (p : Pattern) (guard : d8125 p = 1) : d1005 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1005, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49426 p hg
    simpa only [d8125, d1005, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1005, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47780 p hg
    simpa only [d8125, d1005, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49428 (p : Pattern) (guard : d8126 p = 1) : d1011 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1011, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49424 p hg
    simpa only [d8126, d1011, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1011, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49427 p hg
    simpa only [d8126, d1011, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49429 (p : Pattern) (guard : d8132 p = 1) : d1012 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1012, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49428 p hg
    simpa only [d8132, d1012, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1012, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d8132, d1012, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49430 (p : Pattern) (guard : d8133 p = 1) : d1013 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d1013, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49421 p hg
    simpa only [d8133, d1013, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d1013, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49429 p hg
    simpa only [d8133, d1013, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49431 (p : Pattern) (guard : d8134 p = 1) : d1014 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d1014, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49393 p hg
    simpa only [d8134, d1014, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d1014, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49430 p hg
    simpa only [d8134, d1014, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49432 (p : Pattern) (guard : d8102 p = 1) : d355 p ≤ (0 : Int) + d355 p := by
  omega
theorem compare49433 (p : Pattern) (guard : d8103 p = 1) : d1015 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1015, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34754 p hg
    simpa only [d8103, d1015, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1015, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49432 p hg
    simpa only [d8103, d1015, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49434 (p : Pattern) (guard : d8108 p = 1) : d1016 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1016, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47793 p hg
    simpa only [d8108, d1016, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1016, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49382 p hg
    simpa only [d8108, d1016, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49435 (p : Pattern) (guard : d8109 p = 1) : d1017 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1017, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49433 p hg
    simpa only [d8109, d1017, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1017, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49434 p hg
    simpa only [d8109, d1017, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49436 (p : Pattern) (guard : d8108 p = 1) : d1018 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1018, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47796 p hg
    simpa only [d8108, d1018, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1018, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49356 p hg
    simpa only [d8108, d1018, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49437 (p : Pattern) (guard : d8114 p = 1) : d1019 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1019, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49436 p hg
    simpa only [d8114, d1019, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1019, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49399 p hg
    simpa only [d8114, d1019, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49438 (p : Pattern) (guard : d8115 p = 1) : d1020 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1020, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49435 p hg
    simpa only [d8115, d1020, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1020, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49437 p hg
    simpa only [d8115, d1020, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49439 (p : Pattern) (guard : d8107 p = 1) : d386 p ≤ (0 : Int) + d386 p := by
  omega
theorem compare49440 (p : Pattern) (guard : d8108 p = 1) : d1021 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1021, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34789 p hg
    simpa only [d8108, d1021, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1021, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49439 p hg
    simpa only [d8108, d1021, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49441 (p : Pattern) (guard : d8113 p = 1) : d960 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d960, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47808 p hg
    simpa only [d8113, d960, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d960, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d960, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49442 (p : Pattern) (guard : d8114 p = 1) : d1022 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1022, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49440 p hg
    simpa only [d8114, d1022, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1022, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49441 p hg
    simpa only [d8114, d1022, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49443 (p : Pattern) (guard : d8113 p = 1) : d960 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d960, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47811 p hg
    simpa only [d8113, d960, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d960, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d960, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49444 (p : Pattern) (guard : d8119 p = 1) : d962 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d962, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49443 p hg
    simpa only [d8119, d962, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d962, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49407 p hg
    simpa only [d8119, d962, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49445 (p : Pattern) (guard : d8120 p = 1) : d1023 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1023, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49442 p hg
    simpa only [d8120, d1023, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1023, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49444 p hg
    simpa only [d8120, d1023, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49446 (p : Pattern) (guard : d8121 p = 1) : d1024 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1024, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49438 p hg
    simpa only [d8121, d1024, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1024, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49445 p hg
    simpa only [d8121, d1024, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49447 (p : Pattern) (guard : d8108 p = 1) : d1025 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1025, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34820 p hg
    simpa only [d8108, d1025, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1025, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49382 p hg
    simpa only [d8108, d1025, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49448 (p : Pattern) (guard : d8113 p = 1) : d966 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d966, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47816 p hg
    simpa only [d8113, d966, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d966, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d966, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49449 (p : Pattern) (guard : d8114 p = 1) : d1026 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1026, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49447 p hg
    simpa only [d8114, d1026, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1026, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49448 p hg
    simpa only [d8114, d1026, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49450 (p : Pattern) (guard : d8120 p = 1) : d1027 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1027, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49449 p hg
    simpa only [d8120, d1027, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1027, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49415 p hg
    simpa only [d8120, d1027, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49451 (p : Pattern) (guard : d8113 p = 1) : d966 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d966, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34836 p hg
    simpa only [d8113, d966, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d966, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d966, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49452 (p : Pattern) (guard : d8119 p = 1) : d1004 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1004, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49451 p hg
    simpa only [d8119, d1004, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1004, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47779 p hg
    simpa only [d8119, d1004, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49453 (p : Pattern) (guard : d8125 p = 1) : d1005 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1005, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49452 p hg
    simpa only [d8125, d1005, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1005, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47780 p hg
    simpa only [d8125, d1005, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49454 (p : Pattern) (guard : d8126 p = 1) : d1028 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1028, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49450 p hg
    simpa only [d8126, d1028, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1028, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49453 p hg
    simpa only [d8126, d1028, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49455 (p : Pattern) (guard : d8127 p = 1) : d1029 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1029, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49446 p hg
    simpa only [d8127, d1029, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1029, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49454 p hg
    simpa only [d8127, d1029, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49456 (p : Pattern) (guard : d8108 p = 1) : d965 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d965, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35006 p hg
    simpa only [d8108, d965, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d965, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49402 p hg
    simpa only [d8108, d965, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49457 (p : Pattern) (guard : d8114 p = 1) : d967 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d967, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49456 p hg
    simpa only [d8114, d967, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d967, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49417 p hg
    simpa only [d8114, d967, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49458 (p : Pattern) (guard : d8113 p = 1) : d968 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47827 p hg
    simpa only [d8113, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d968, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49459 (p : Pattern) (guard : d8119 p = 1) : d969 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d969, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49458 p hg
    simpa only [d8119, d969, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d969, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d969, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49460 (p : Pattern) (guard : d8120 p = 1) : d970 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d970, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49457 p hg
    simpa only [d8120, d970, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d970, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49459 p hg
    simpa only [d8120, d970, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49461 (p : Pattern) (guard : d8112 p = 1) : d374 p ≤ (0 : Int) + d374 p := by
  omega
theorem compare49462 (p : Pattern) (guard : d8113 p = 1) : d971 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d971, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d8113, d971, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d971, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d8113, d971, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49463 (p : Pattern) (guard : d8119 p = 1) : d973 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d973, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49462 p hg
    simpa only [d8119, d973, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d973, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47779 p hg
    simpa only [d8119, d973, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49464 (p : Pattern) (guard : d8125 p = 1) : d975 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d975, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49463 p hg
    simpa only [d8125, d975, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d975, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47780 p hg
    simpa only [d8125, d975, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49465 (p : Pattern) (guard : d8126 p = 1) : d976 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d976, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d8126, d976, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d976, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49464 p hg
    simpa only [d8126, d976, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49466 (p : Pattern) (guard : d8113 p = 1) : d985 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d985, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38148 p hg
    simpa only [d8113, d985, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d985, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d985, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49467 (p : Pattern) (guard : d8119 p = 1) : d986 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d986, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49466 p hg
    simpa only [d8119, d986, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d986, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38150 p hg
    simpa only [d8119, d986, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49468 (p : Pattern) (guard : d8125 p = 1) : d987 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d987, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49467 p hg
    simpa only [d8125, d987, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d987, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38152 p hg
    simpa only [d8125, d987, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49469 (p : Pattern) (guard : d8131 p = 1) : d988 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d988, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49468 p hg
    simpa only [d8131, d988, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d988, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41400 p hg
    simpa only [d8131, d988, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49470 (p : Pattern) (guard : d8132 p = 1) : d1030 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1030, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49465 p hg
    simpa only [d8132, d1030, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1030, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49469 p hg
    simpa only [d8132, d1030, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49471 (p : Pattern) (guard : d8133 p = 1) : d1031 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d1031, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49455 p hg
    simpa only [d8133, d1031, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d1031, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49470 p hg
    simpa only [d8133, d1031, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49472 (p : Pattern) (guard : d8107 p = 1) : d389 p ≤ (0 : Int) + d389 p := by
  omega
theorem compare49473 (p : Pattern) (guard : d8108 p = 1) : d978 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d978, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34848 p hg
    simpa only [d8108, d978, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d978, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49472 p hg
    simpa only [d8108, d978, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49474 (p : Pattern) (guard : d8113 p = 1) : d992 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d992, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47839 p hg
    simpa only [d8113, d992, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d992, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d992, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49475 (p : Pattern) (guard : d8114 p = 1) : d1032 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1032, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49473 p hg
    simpa only [d8114, d1032, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1032, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49474 p hg
    simpa only [d8114, d1032, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49476 (p : Pattern) (guard : d8113 p = 1) : d994 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d994, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47842 p hg
    simpa only [d8113, d994, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d994, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d994, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49477 (p : Pattern) (guard : d8118 p = 1) : d954 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d8118, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49478 (p : Pattern) (guard : d8119 p = 1) : d995 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d995, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49476 p hg
    simpa only [d8119, d995, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d995, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49477 p hg
    simpa only [d8119, d995, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49479 (p : Pattern) (guard : d8120 p = 1) : d1033 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1033, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49475 p hg
    simpa only [d8120, d1033, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1033, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49478 p hg
    simpa only [d8120, d1033, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49480 (p : Pattern) (guard : d8112 p = 1) : d371 p ≤ (0 : Int) + d371 p := by
  omega
theorem compare49481 (p : Pattern) (guard : d8113 p = 1) : d981 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d981, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d8113, d981, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d981, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49480 p hg
    simpa only [d8113, d981, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49482 (p : Pattern) (guard : d8118 p = 1) : d960 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d960, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47849 p hg
    simpa only [d8118, d960, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d960, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d960, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49483 (p : Pattern) (guard : d8119 p = 1) : d1034 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1034, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49481 p hg
    simpa only [d8119, d1034, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1034, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49482 p hg
    simpa only [d8119, d1034, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49484 (p : Pattern) (guard : d8118 p = 1) : d960 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47852 p hg
    simpa only [d8118, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49485 (p : Pattern) (guard : d8123 p = 1) : d961 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41453 p hg
    simpa only [d8123, d961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49486 (p : Pattern) (guard : d8124 p = 1) : d962 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49484 p hg
    simpa only [d8124, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49485 p hg
    simpa only [d8124, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49487 (p : Pattern) (guard : d8125 p = 1) : d1035 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1035, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49483 p hg
    simpa only [d8125, d1035, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1035, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49486 p hg
    simpa only [d8125, d1035, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49488 (p : Pattern) (guard : d8126 p = 1) : d1036 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1036, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49479 p hg
    simpa only [d8126, d1036, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1036, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49487 p hg
    simpa only [d8126, d1036, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49489 (p : Pattern) (guard : d8113 p = 1) : d1001 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1001, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34910 p hg
    simpa only [d8113, d1001, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1001, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d1001, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49490 (p : Pattern) (guard : d8118 p = 1) : d966 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47858 p hg
    simpa only [d8118, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49491 (p : Pattern) (guard : d8119 p = 1) : d1002 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1002, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49489 p hg
    simpa only [d8119, d1002, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1002, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49490 p hg
    simpa only [d8119, d1002, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49492 (p : Pattern) (guard : d8118 p = 1) : d968 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47861 p hg
    simpa only [d8118, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49493 (p : Pattern) (guard : d8124 p = 1) : d969 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49492 p hg
    simpa only [d8124, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49494 (p : Pattern) (guard : d8125 p = 1) : d1003 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1003, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49491 p hg
    simpa only [d8125, d1003, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1003, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49493 p hg
    simpa only [d8125, d1003, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49495 (p : Pattern) (guard : d8118 p = 1) : d966 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d966, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34929 p hg
    simpa only [d8118, d966, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d966, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d966, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49496 (p : Pattern) (guard : d8124 p = 1) : d1004 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1004, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49495 p hg
    simpa only [d8124, d1004, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1004, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47870 p hg
    simpa only [d8124, d1004, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49497 (p : Pattern) (guard : d8130 p = 1) : d1005 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1005, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49496 p hg
    simpa only [d8130, d1005, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1005, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47871 p hg
    simpa only [d8130, d1005, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49498 (p : Pattern) (guard : d8131 p = 1) : d1006 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1006, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49494 p hg
    simpa only [d8131, d1006, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1006, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49497 p hg
    simpa only [d8131, d1006, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49499 (p : Pattern) (guard : d8132 p = 1) : d1037 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1037, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49488 p hg
    simpa only [d8132, d1037, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1037, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49498 p hg
    simpa only [d8132, d1037, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49500 (p : Pattern) (guard : d8113 p = 1) : d1001 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1001, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35065 p hg
    simpa only [d8113, d1001, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1001, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d1001, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49501 (p : Pattern) (guard : d8119 p = 1) : d1002 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1002, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49500 p hg
    simpa only [d8119, d1002, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1002, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49490 p hg
    simpa only [d8119, d1002, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49502 (p : Pattern) (guard : d8125 p = 1) : d1003 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1003, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49501 p hg
    simpa only [d8125, d1003, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1003, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49493 p hg
    simpa only [d8125, d1003, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49503 (p : Pattern) (guard : d8118 p = 1) : d966 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35074 p hg
    simpa only [d8118, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d966, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49504 (p : Pattern) (guard : d8124 p = 1) : d1004 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1004, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49503 p hg
    simpa only [d8124, d1004, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1004, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47870 p hg
    simpa only [d8124, d1004, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49505 (p : Pattern) (guard : d8130 p = 1) : d1005 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1005, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49504 p hg
    simpa only [d8130, d1005, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1005, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47871 p hg
    simpa only [d8130, d1005, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49506 (p : Pattern) (guard : d8131 p = 1) : d1006 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1006, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49502 p hg
    simpa only [d8131, d1006, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1006, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49505 p hg
    simpa only [d8131, d1006, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49507 (p : Pattern) (guard : d8137 p = 1) : d1038 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1038, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49506 p hg
    simpa only [d8137, d1038, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1038, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d1038, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49508 (p : Pattern) (guard : d8138 p = 1) : d1039 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1039, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49499 p hg
    simpa only [d8138, d1039, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1039, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49507 p hg
    simpa only [d8138, d1039, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49509 (p : Pattern) (guard : d8139 p = 1) : d1040 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d1040, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49471 p hg
    simpa only [d8139, d1040, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d1040, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49508 p hg
    simpa only [d8139, d1040, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49510 (p : Pattern) (guard : d8140 p = 1) : d1041 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d1041, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49431 p hg
    simpa only [d8140, d1041, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d1041, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49509 p hg
    simpa only [d8140, d1041, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49511 (p : Pattern) (guard : d8102 p = 1) : d346 p ≤ (0 : Int) + d346 p := by
  omega
theorem compare49512 (p : Pattern) (guard : d8103 p = 1) : d949 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d949, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34949 p hg
    simpa only [d8103, d949, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d949, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49511 p hg
    simpa only [d8103, d949, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49513 (p : Pattern) (guard : d8108 p = 1) : d951 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d951, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47886 p hg
    simpa only [d8108, d951, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d951, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49402 p hg
    simpa only [d8108, d951, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49514 (p : Pattern) (guard : d8109 p = 1) : d952 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d952, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49512 p hg
    simpa only [d8109, d952, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d952, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49513 p hg
    simpa only [d8109, d952, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49515 (p : Pattern) (guard : d8108 p = 1) : d953 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d953, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47889 p hg
    simpa only [d8108, d953, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d953, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49382 p hg
    simpa only [d8108, d953, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49516 (p : Pattern) (guard : d8113 p = 1) : d954 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d954, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34961 p hg
    simpa only [d8113, d954, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d954, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d954, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49517 (p : Pattern) (guard : d8114 p = 1) : d955 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d955, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49515 p hg
    simpa only [d8114, d955, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d955, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49516 p hg
    simpa only [d8114, d955, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49518 (p : Pattern) (guard : d8115 p = 1) : d956 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d956, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49514 p hg
    simpa only [d8115, d956, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d956, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49517 p hg
    simpa only [d8115, d956, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49519 (p : Pattern) (guard : d8107 p = 1) : d369 p ≤ (0 : Int) + d369 p := by
  omega
theorem compare49520 (p : Pattern) (guard : d8108 p = 1) : d957 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d957, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34973 p hg
    simpa only [d8108, d957, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d957, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49519 p hg
    simpa only [d8108, d957, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49521 (p : Pattern) (guard : d8113 p = 1) : d958 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d958, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47897 p hg
    simpa only [d8113, d958, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d958, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d8113, d958, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49522 (p : Pattern) (guard : d8114 p = 1) : d959 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d959, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49520 p hg
    simpa only [d8114, d959, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d959, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49521 p hg
    simpa only [d8114, d959, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49523 (p : Pattern) (guard : d8119 p = 1) : d962 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d962, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49441 p hg
    simpa only [d8119, d962, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d962, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49407 p hg
    simpa only [d8119, d962, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49524 (p : Pattern) (guard : d8120 p = 1) : d963 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d963, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49522 p hg
    simpa only [d8120, d963, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d963, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49523 p hg
    simpa only [d8120, d963, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49525 (p : Pattern) (guard : d8121 p = 1) : d964 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d964, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49518 p hg
    simpa only [d8121, d964, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d964, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49524 p hg
    simpa only [d8121, d964, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49526 (p : Pattern) (guard : d8127 p = 1) : d977 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d977, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49525 p hg
    simpa only [d8127, d977, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d977, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49465 p hg
    simpa only [d8127, d977, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49527 (p : Pattern) (guard : d8114 p = 1) : d979 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d979, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49473 p hg
    simpa only [d8114, d979, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d979, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49425 p hg
    simpa only [d8114, d979, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49528 (p : Pattern) (guard : d8113 p = 1) : d968 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47907 p hg
    simpa only [d8113, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d968, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49529 (p : Pattern) (guard : d8119 p = 1) : d969 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d969, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49528 p hg
    simpa only [d8119, d969, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d969, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d969, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49530 (p : Pattern) (guard : d8120 p = 1) : d980 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d980, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49527 p hg
    simpa only [d8120, d980, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d980, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49529 p hg
    simpa only [d8120, d980, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49531 (p : Pattern) (guard : d8118 p = 1) : d972 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d972, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47911 p hg
    simpa only [d8118, d972, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d972, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d972, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49532 (p : Pattern) (guard : d8119 p = 1) : d982 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d982, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49481 p hg
    simpa only [d8119, d982, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d982, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49531 p hg
    simpa only [d8119, d982, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49533 (p : Pattern) (guard : d8125 p = 1) : d983 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d983, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49532 p hg
    simpa only [d8125, d983, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d983, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47780 p hg
    simpa only [d8125, d983, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49534 (p : Pattern) (guard : d8126 p = 1) : d984 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d984, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49530 p hg
    simpa only [d8126, d984, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d984, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49533 p hg
    simpa only [d8126, d984, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49535 (p : Pattern) (guard : d8113 p = 1) : d985 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d985, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38177 p hg
    simpa only [d8113, d985, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d985, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d985, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49536 (p : Pattern) (guard : d8119 p = 1) : d986 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d986, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49535 p hg
    simpa only [d8119, d986, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d986, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38150 p hg
    simpa only [d8119, d986, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49537 (p : Pattern) (guard : d8125 p = 1) : d987 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d987, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49536 p hg
    simpa only [d8125, d987, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d987, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38152 p hg
    simpa only [d8125, d987, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49538 (p : Pattern) (guard : d8131 p = 1) : d988 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d988, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49537 p hg
    simpa only [d8131, d988, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d988, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41412 p hg
    simpa only [d8131, d988, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49539 (p : Pattern) (guard : d8132 p = 1) : d989 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d989, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49534 p hg
    simpa only [d8132, d989, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d989, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49538 p hg
    simpa only [d8132, d989, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49540 (p : Pattern) (guard : d8133 p = 1) : d990 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d990, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49526 p hg
    simpa only [d8133, d990, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d990, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49539 p hg
    simpa only [d8133, d990, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49541 (p : Pattern) (guard : d8108 p = 1) : d991 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d991, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35029 p hg
    simpa only [d8108, d991, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d991, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49439 p hg
    simpa only [d8108, d991, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49542 (p : Pattern) (guard : d8113 p = 1) : d992 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d992, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47919 p hg
    simpa only [d8113, d992, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d992, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d992, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49543 (p : Pattern) (guard : d8114 p = 1) : d993 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d993, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49541 p hg
    simpa only [d8114, d993, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d993, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49542 p hg
    simpa only [d8114, d993, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49544 (p : Pattern) (guard : d8113 p = 1) : d994 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d994, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47922 p hg
    simpa only [d8113, d994, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d994, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d994, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49545 (p : Pattern) (guard : d8119 p = 1) : d995 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d995, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49544 p hg
    simpa only [d8119, d995, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d995, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49477 p hg
    simpa only [d8119, d995, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49546 (p : Pattern) (guard : d8120 p = 1) : d996 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d996, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49543 p hg
    simpa only [d8120, d996, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d996, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49545 p hg
    simpa only [d8120, d996, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49547 (p : Pattern) (guard : d8112 p = 1) : d361 p ≤ (0 : Int) + d361 p := by
  omega
theorem compare49548 (p : Pattern) (guard : d8113 p = 1) : d997 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d997, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35048 p hg
    simpa only [d8113, d997, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d997, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49547 p hg
    simpa only [d8113, d997, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49549 (p : Pattern) (guard : d8118 p = 1) : d960 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d960, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47928 p hg
    simpa only [d8118, d960, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d960, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d960, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49550 (p : Pattern) (guard : d8119 p = 1) : d998 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d998, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49548 p hg
    simpa only [d8119, d998, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d998, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49549 p hg
    simpa only [d8119, d998, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49551 (p : Pattern) (guard : d8124 p = 1) : d962 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d962, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49482 p hg
    simpa only [d8124, d962, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d962, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49485 p hg
    simpa only [d8124, d962, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49552 (p : Pattern) (guard : d8125 p = 1) : d999 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d999, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49550 p hg
    simpa only [d8125, d999, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d999, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49551 p hg
    simpa only [d8125, d999, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49553 (p : Pattern) (guard : d8126 p = 1) : d1000 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1000, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49546 p hg
    simpa only [d8126, d1000, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1000, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49552 p hg
    simpa only [d8126, d1000, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49554 (p : Pattern) (guard : d8132 p = 1) : d1007 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1007, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49553 p hg
    simpa only [d8132, d1007, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1007, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49506 p hg
    simpa only [d8132, d1007, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49555 (p : Pattern) (guard : d8113 p = 1) : d1008 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1008, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38187 p hg
    simpa only [d8113, d1008, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1008, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d8113, d1008, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49556 (p : Pattern) (guard : d8119 p = 1) : d1009 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1009, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49555 p hg
    simpa only [d8119, d1009, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1009, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49490 p hg
    simpa only [d8119, d1009, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49557 (p : Pattern) (guard : d8125 p = 1) : d1010 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1010, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49556 p hg
    simpa only [d8125, d1010, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1010, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49493 p hg
    simpa only [d8125, d1010, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49558 (p : Pattern) (guard : d8118 p = 1) : d966 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41416 p hg
    simpa only [d8118, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d966, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49559 (p : Pattern) (guard : d8124 p = 1) : d1004 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1004, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49558 p hg
    simpa only [d8124, d1004, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1004, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47870 p hg
    simpa only [d8124, d1004, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
