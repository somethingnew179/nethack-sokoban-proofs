/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons296
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare41580 (p : Pattern) (guard : d8111 p = 1) : d524 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41579 p hg
    simpa only [d8111, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41581 (p : Pattern) (guard : d8112 p = 1) : d525 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41578 p hg
    simpa only [d8112, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41580 p hg
    simpa only [d8112, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41582 (p : Pattern) (guard : d8113 p = 1) : d526 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41577 p hg
    simpa only [d8113, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41581 p hg
    simpa only [d8113, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41583 (p : Pattern) (guard : d8118 p = 1) : d529 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41581 p hg
    simpa only [d8118, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38911 p hg
    simpa only [d8118, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41584 (p : Pattern) (guard : d8119 p = 1) : d530 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41582 p hg
    simpa only [d8119, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41583 p hg
    simpa only [d8119, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41585 (p : Pattern) (guard : d8120 p = 1) : d531 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d531, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38134 p hg
    simpa only [d8120, d531, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d531, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d8120, d531, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41586 (p : Pattern) (guard : d8105 p = 1) : d532 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34678 p hg
    simpa only [d8105, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11542 p hg
    simpa only [d8105, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41587 (p : Pattern) (guard : d8111 p = 1) : d533 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41586 p hg
    simpa only [d8111, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41588 (p : Pattern) (guard : d8112 p = 1) : d534 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41576 p hg
    simpa only [d8112, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41587 p hg
    simpa only [d8112, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41589 (p : Pattern) (guard : d8117 p = 1) : d535 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41580 p hg
    simpa only [d8117, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38933 p hg
    simpa only [d8117, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41590 (p : Pattern) (guard : d8118 p = 1) : d536 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41588 p hg
    simpa only [d8118, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41589 p hg
    simpa only [d8118, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41591 (p : Pattern) (guard : d8117 p = 1) : d537 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41580 p hg
    simpa only [d8117, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38936 p hg
    simpa only [d8117, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41592 (p : Pattern) (guard : d8123 p = 1) : d540 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41591 p hg
    simpa only [d8123, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38938 p hg
    simpa only [d8123, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41593 (p : Pattern) (guard : d8124 p = 1) : d541 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41590 p hg
    simpa only [d8124, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41592 p hg
    simpa only [d8124, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41594 (p : Pattern) (guard : d8125 p = 1) : d542 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d542, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41394 p hg
    simpa only [d8125, d542, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d542, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41593 p hg
    simpa only [d8125, d542, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41595 (p : Pattern) (guard : d8126 p = 1) : d543 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d543, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41585 p hg
    simpa only [d8126, d543, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d543, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41594 p hg
    simpa only [d8126, d543, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41596 (p : Pattern) (guard : d8132 p = 1) : d547 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d547, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41595 p hg
    simpa only [d8132, d547, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d547, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d8132, d547, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41597 (p : Pattern) (guard : d8133 p = 1) : d548 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d548, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41573 p hg
    simpa only [d8133, d548, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d548, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41596 p hg
    simpa only [d8133, d548, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41598 (p : Pattern) (guard : d8134 p = 1) : d549 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d549, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41571 p hg
    simpa only [d8134, d549, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d549, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41597 p hg
    simpa only [d8134, d549, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41599 (p : Pattern) (guard : d8126 p = 1) : d439 p ≤ (0 : Int) + d439 p := by
  omega
theorem compare41600 (p : Pattern) (guard : d8127 p = 1) : d550 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d550, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34818 p hg
    simpa only [d8127, d550, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d550, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41599 p hg
    simpa only [d8127, d550, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41601 (p : Pattern) (guard : d8095 p = 1) : d518 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d518, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34675 p hg
    simpa only [d8095, d518, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d518, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d8095, d518, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41602 (p : Pattern) (guard : d8101 p = 1) : d519 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d519, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41601 p hg
    simpa only [d8101, d519, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d519, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34570 p hg
    simpa only [d8101, d519, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41603 (p : Pattern) (guard : d8107 p = 1) : d521 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d521, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41602 p hg
    simpa only [d8107, d521, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d521, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41576 p hg
    simpa only [d8107, d521, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41604 (p : Pattern) (guard : d8113 p = 1) : d526 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d526, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41603 p hg
    simpa only [d8113, d526, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d526, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41581 p hg
    simpa only [d8113, d526, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41605 (p : Pattern) (guard : d8119 p = 1) : d530 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d530, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41604 p hg
    simpa only [d8119, d530, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d530, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41583 p hg
    simpa only [d8119, d530, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41606 (p : Pattern) (guard : d8120 p = 1) : d531 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d531, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35009 p hg
    simpa only [d8120, d531, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d531, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41605 p hg
    simpa only [d8120, d531, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41607 (p : Pattern) (guard : d8125 p = 1) : d542 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d542, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35023 p hg
    simpa only [d8125, d542, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d542, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41593 p hg
    simpa only [d8125, d542, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41608 (p : Pattern) (guard : d8126 p = 1) : d543 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d543, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41606 p hg
    simpa only [d8126, d543, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d543, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41607 p hg
    simpa only [d8126, d543, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41609 (p : Pattern) (guard : d8131 p = 1) : d441 p ≤ (0 : Int) + d441 p := by
  omega
theorem compare41610 (p : Pattern) (guard : d8132 p = 1) : d551 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d551, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41608 p hg
    simpa only [d8132, d551, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d551, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41609 p hg
    simpa only [d8132, d551, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41611 (p : Pattern) (guard : d8133 p = 1) : d552 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d552, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41600 p hg
    simpa only [d8133, d552, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d552, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41610 p hg
    simpa only [d8133, d552, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41612 (p : Pattern) (guard : d8131 p = 1) : d412 p ≤ (0 : Int) + d412 p := by
  omega
theorem compare41613 (p : Pattern) (guard : d8132 p = 1) : d553 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d553, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34907 p hg
    simpa only [d8132, d553, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d553, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41612 p hg
    simpa only [d8132, d553, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41614 (p : Pattern) (guard : d8106 p = 1) : d519 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41575 p hg
    simpa only [d8106, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34711 p hg
    simpa only [d8106, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41615 (p : Pattern) (guard : d8105 p = 1) : d518 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d8105, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d8105, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41616 (p : Pattern) (guard : d8111 p = 1) : d520 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41615 p hg
    simpa only [d8111, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5081 p hg
    simpa only [d8111, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41617 (p : Pattern) (guard : d8112 p = 1) : d521 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41614 p hg
    simpa only [d8112, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41616 p hg
    simpa only [d8112, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41618 (p : Pattern) (guard : d8111 p = 1) : d522 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41615 p hg
    simpa only [d8111, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41619 (p : Pattern) (guard : d0 p = 1) : d524 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41620 (p : Pattern) (guard : d8117 p = 1) : d525 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41618 p hg
    simpa only [d8117, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41619 p hg
    simpa only [d8117, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41621 (p : Pattern) (guard : d8118 p = 1) : d526 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41617 p hg
    simpa only [d8118, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41620 p hg
    simpa only [d8118, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41622 (p : Pattern) (guard : d8123 p = 1) : d529 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41620 p hg
    simpa only [d8123, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39709 p hg
    simpa only [d8123, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41623 (p : Pattern) (guard : d8124 p = 1) : d530 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41621 p hg
    simpa only [d8124, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41622 p hg
    simpa only [d8124, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41624 (p : Pattern) (guard : d8125 p = 1) : d531 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d531, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35067 p hg
    simpa only [d8125, d531, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d531, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41623 p hg
    simpa only [d8125, d531, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41625 (p : Pattern) (guard : d0 p = 1) : d533 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41626 (p : Pattern) (guard : d8117 p = 1) : d534 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41616 p hg
    simpa only [d8117, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41625 p hg
    simpa only [d8117, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41627 (p : Pattern) (guard : d0 p = 1) : d535 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41628 (p : Pattern) (guard : d8123 p = 1) : d536 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41626 p hg
    simpa only [d8123, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41627 p hg
    simpa only [d8123, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41629 (p : Pattern) (guard : d0 p = 1) : d540 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41630 (p : Pattern) (guard : d8129 p = 1) : d541 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41628 p hg
    simpa only [d8129, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41629 p hg
    simpa only [d8129, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41631 (p : Pattern) (guard : d8130 p = 1) : d542 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d542, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35076 p hg
    simpa only [d8130, d542, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d542, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41630 p hg
    simpa only [d8130, d542, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41632 (p : Pattern) (guard : d8131 p = 1) : d543 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d543, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41624 p hg
    simpa only [d8131, d543, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d543, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41631 p hg
    simpa only [d8131, d543, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41633 (p : Pattern) (guard : d8137 p = 1) : d547 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d547, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41632 p hg
    simpa only [d8137, d547, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d547, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d547, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41634 (p : Pattern) (guard : d8138 p = 1) : d554 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d554, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41613 p hg
    simpa only [d8138, d554, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d554, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41633 p hg
    simpa only [d8138, d554, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41635 (p : Pattern) (guard : d8139 p = 1) : d555 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d555, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41611 p hg
    simpa only [d8139, d555, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d555, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41634 p hg
    simpa only [d8139, d555, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41636 (p : Pattern) (guard : d8140 p = 1) : d556 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d556, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41598 p hg
    simpa only [d8140, d556, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d556, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41635 p hg
    simpa only [d8140, d556, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41637 (p : Pattern) (guard : d8126 p = 1) : d400 p ≤ (0 : Int) + d400 p := by
  omega
theorem compare41638 (p : Pattern) (guard : d8127 p = 1) : d517 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d517, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35005 p hg
    simpa only [d8127, d517, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d517, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41637 p hg
    simpa only [d8127, d517, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41639 (p : Pattern) (guard : d8095 p = 1) : d518 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d518, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34718 p hg
    simpa only [d8095, d518, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d518, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d8095, d518, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41640 (p : Pattern) (guard : d8101 p = 1) : d519 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d519, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41639 p hg
    simpa only [d8101, d519, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d519, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34570 p hg
    simpa only [d8101, d519, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41641 (p : Pattern) (guard : d8107 p = 1) : d521 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41640 p hg
    simpa only [d8107, d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41576 p hg
    simpa only [d8107, d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41642 (p : Pattern) (guard : d8113 p = 1) : d526 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d526, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41641 p hg
    simpa only [d8113, d526, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d526, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41581 p hg
    simpa only [d8113, d526, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41643 (p : Pattern) (guard : d8119 p = 1) : d530 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d530, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41642 p hg
    simpa only [d8119, d530, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d530, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41583 p hg
    simpa only [d8119, d530, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41644 (p : Pattern) (guard : d8120 p = 1) : d531 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d531, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34858 p hg
    simpa only [d8120, d531, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d531, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41643 p hg
    simpa only [d8120, d531, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41645 (p : Pattern) (guard : d8125 p = 1) : d542 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d542, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34895 p hg
    simpa only [d8125, d542, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d542, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41593 p hg
    simpa only [d8125, d542, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41646 (p : Pattern) (guard : d8126 p = 1) : d543 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d543, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41644 p hg
    simpa only [d8126, d543, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d543, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41645 p hg
    simpa only [d8126, d543, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41647 (p : Pattern) (guard : d8132 p = 1) : d544 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d544, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41646 p hg
    simpa only [d8132, d544, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d544, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41612 p hg
    simpa only [d8132, d544, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41648 (p : Pattern) (guard : d8133 p = 1) : d545 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d545, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41638 p hg
    simpa only [d8133, d545, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d545, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41647 p hg
    simpa only [d8133, d545, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41649 (p : Pattern) (guard : d8131 p = 1) : d422 p ≤ (0 : Int) + d422 p := by
  omega
theorem compare41650 (p : Pattern) (guard : d8132 p = 1) : d546 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d546, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35064 p hg
    simpa only [d8132, d546, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d546, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41649 p hg
    simpa only [d8132, d546, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41651 (p : Pattern) (guard : d8125 p = 1) : d531 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d531, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38189 p hg
    simpa only [d8125, d531, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d531, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41623 p hg
    simpa only [d8125, d531, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41652 (p : Pattern) (guard : d8130 p = 1) : d542 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d542, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41418 p hg
    simpa only [d8130, d542, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d542, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41630 p hg
    simpa only [d8130, d542, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41653 (p : Pattern) (guard : d8131 p = 1) : d543 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d543, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41651 p hg
    simpa only [d8131, d543, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d543, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41652 p hg
    simpa only [d8131, d543, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41654 (p : Pattern) (guard : d8137 p = 1) : d547 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d547, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41653 p hg
    simpa only [d8137, d547, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d547, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d547, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41655 (p : Pattern) (guard : d8138 p = 1) : d548 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d548, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41650 p hg
    simpa only [d8138, d548, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d548, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41654 p hg
    simpa only [d8138, d548, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41656 (p : Pattern) (guard : d8139 p = 1) : d549 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d549, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41648 p hg
    simpa only [d8139, d549, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d549, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41655 p hg
    simpa only [d8139, d549, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41657 (p : Pattern) (guard : d8131 p = 1) : d439 p ≤ (0 : Int) + d439 p := by
  omega
theorem compare41658 (p : Pattern) (guard : d8132 p = 1) : d557 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d557, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35251 p hg
    simpa only [d8132, d557, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d557, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41657 p hg
    simpa only [d8132, d557, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41659 (p : Pattern) (guard : d8100 p = 1) : d558 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d558, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35117 p hg
    simpa only [d8100, d558, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d558, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35137 p hg
    simpa only [d8100, d558, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41660 (p : Pattern) (guard : d8106 p = 1) : d559 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d559, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41659 p hg
    simpa only [d8106, d559, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d559, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35184 p hg
    simpa only [d8106, d559, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41661 (p : Pattern) (guard : d8105 p = 1) : d558 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35178 p hg
    simpa only [d8105, d558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d8105, d558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41662 (p : Pattern) (guard : d8111 p = 1) : d560 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41661 p hg
    simpa only [d8111, d560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5067 p hg
    simpa only [d8111, d560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41663 (p : Pattern) (guard : d8112 p = 1) : d561 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d561, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41660 p hg
    simpa only [d8112, d561, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d561, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41662 p hg
    simpa only [d8112, d561, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41664 (p : Pattern) (guard : d8111 p = 1) : d562 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41661 p hg
    simpa only [d8111, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41665 (p : Pattern) (guard : d0 p = 1) : d564 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41666 (p : Pattern) (guard : d8117 p = 1) : d565 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41664 p hg
    simpa only [d8117, d565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41665 p hg
    simpa only [d8117, d565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41667 (p : Pattern) (guard : d8118 p = 1) : d566 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d566, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41663 p hg
    simpa only [d8118, d566, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d566, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41666 p hg
    simpa only [d8118, d566, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41668 (p : Pattern) (guard : d8123 p = 1) : d567 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41666 p hg
    simpa only [d8123, d567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4396 p hg
    simpa only [d8123, d567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41669 (p : Pattern) (guard : d8124 p = 1) : d568 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d568, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41667 p hg
    simpa only [d8124, d568, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d568, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41668 p hg
    simpa only [d8124, d568, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41670 (p : Pattern) (guard : d8125 p = 1) : d569 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d569, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38204 p hg
    simpa only [d8125, d569, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d569, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41669 p hg
    simpa only [d8125, d569, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41671 (p : Pattern) (guard : d0 p = 1) : d571 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41672 (p : Pattern) (guard : d8117 p = 1) : d572 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41662 p hg
    simpa only [d8117, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41671 p hg
    simpa only [d8117, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41673 (p : Pattern) (guard : d0 p = 1) : d573 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41674 (p : Pattern) (guard : d8123 p = 1) : d574 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41672 p hg
    simpa only [d8123, d574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41673 p hg
    simpa only [d8123, d574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41675 (p : Pattern) (guard : d0 p = 1) : d576 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41676 (p : Pattern) (guard : d8129 p = 1) : d577 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41674 p hg
    simpa only [d8129, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41675 p hg
    simpa only [d8129, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41677 (p : Pattern) (guard : d8130 p = 1) : d578 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d578, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41429 p hg
    simpa only [d8130, d578, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d578, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41676 p hg
    simpa only [d8130, d578, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41678 (p : Pattern) (guard : d8131 p = 1) : d579 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d579, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41670 p hg
    simpa only [d8131, d579, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d579, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41677 p hg
    simpa only [d8131, d579, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41679 (p : Pattern) (guard : d8136 p = 1) : d441 p ≤ (0 : Int) + d441 p := by
  omega
theorem compare41680 (p : Pattern) (guard : d8137 p = 1) : d580 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d580, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41678 p hg
    simpa only [d8137, d580, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d580, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41679 p hg
    simpa only [d8137, d580, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41681 (p : Pattern) (guard : d8138 p = 1) : d581 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d581, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41658 p hg
    simpa only [d8138, d581, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d581, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41680 p hg
    simpa only [d8138, d581, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41682 (p : Pattern) (guard : d8136 p = 1) : d412 p ≤ (0 : Int) + d412 p := by
  omega
theorem compare41683 (p : Pattern) (guard : d8137 p = 1) : d582 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d582, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35353 p hg
    simpa only [d8137, d582, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d582, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41682 p hg
    simpa only [d8137, d582, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41684 (p : Pattern) (guard : d8111 p = 1) : d559 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41661 p hg
    simpa only [d8111, d559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5173 p hg
    simpa only [d8111, d559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41685 (p : Pattern) (guard : d0 p = 1) : d560 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41686 (p : Pattern) (guard : d8117 p = 1) : d561 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41684 p hg
    simpa only [d8117, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41685 p hg
    simpa only [d8117, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41687 (p : Pattern) (guard : d0 p = 1) : d565 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41688 (p : Pattern) (guard : d8123 p = 1) : d566 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41686 p hg
    simpa only [d8123, d566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41687 p hg
    simpa only [d8123, d566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41689 (p : Pattern) (guard : d0 p = 1) : d567 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41690 (p : Pattern) (guard : d8129 p = 1) : d568 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41688 p hg
    simpa only [d8129, d568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41689 p hg
    simpa only [d8129, d568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41691 (p : Pattern) (guard : d8130 p = 1) : d569 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d569, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38230 p hg
    simpa only [d8130, d569, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d569, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41690 p hg
    simpa only [d8130, d569, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41692 (p : Pattern) (guard : d8135 p = 1) : d578 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d578, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41436 p hg
    simpa only [d8135, d578, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d578, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2843 p hg
    simpa only [d8135, d578, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41693 (p : Pattern) (guard : d8136 p = 1) : d579 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d579, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41691 p hg
    simpa only [d8136, d579, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d579, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41692 p hg
    simpa only [d8136, d579, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41694 (p : Pattern) (guard : d8142 p = 1) : d583 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d583, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41693 p hg
    simpa only [d8142, d583, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d583, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d583, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41695 (p : Pattern) (guard : d8143 p = 1) : d584 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d584, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41683 p hg
    simpa only [d8143, d584, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d584, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41694 p hg
    simpa only [d8143, d584, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41696 (p : Pattern) (guard : d8144 p = 1) : d585 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d585, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41681 p hg
    simpa only [d8144, d585, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d585, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41695 p hg
    simpa only [d8144, d585, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41697 (p : Pattern) (guard : d8145 p = 1) : d586 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d586, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41656 p hg
    simpa only [d8145, d586, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d586, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41696 p hg
    simpa only [d8145, d586, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41698 (p : Pattern) (guard : d8146 p = 1) : d587 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41636 p hg
    simpa only [d8146, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41697 p hg
    simpa only [d8146, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41699 (p : Pattern) (guard : d8132 p = 1) : d550 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d550, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35453 p hg
    simpa only [d8132, d550, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d550, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41657 p hg
    simpa only [d8132, d550, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41700 (p : Pattern) (guard : d8100 p = 1) : d518 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d518, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34925 p hg
    simpa only [d8100, d518, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d518, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d8100, d518, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41701 (p : Pattern) (guard : d8106 p = 1) : d519 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d519, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41700 p hg
    simpa only [d8106, d519, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d519, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34711 p hg
    simpa only [d8106, d519, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41702 (p : Pattern) (guard : d8112 p = 1) : d521 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d521, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41701 p hg
    simpa only [d8112, d521, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d521, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41616 p hg
    simpa only [d8112, d521, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41703 (p : Pattern) (guard : d8118 p = 1) : d526 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d526, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41702 p hg
    simpa only [d8118, d526, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d526, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41620 p hg
    simpa only [d8118, d526, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41704 (p : Pattern) (guard : d8124 p = 1) : d530 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d530, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41703 p hg
    simpa only [d8124, d530, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d530, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41622 p hg
    simpa only [d8124, d530, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41705 (p : Pattern) (guard : d8125 p = 1) : d531 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d531, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35619 p hg
    simpa only [d8125, d531, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d531, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41704 p hg
    simpa only [d8125, d531, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41706 (p : Pattern) (guard : d8130 p = 1) : d542 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d542, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35633 p hg
    simpa only [d8130, d542, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d542, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41630 p hg
    simpa only [d8130, d542, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41707 (p : Pattern) (guard : d8131 p = 1) : d543 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d543, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41705 p hg
    simpa only [d8131, d543, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d543, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41706 p hg
    simpa only [d8131, d543, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41708 (p : Pattern) (guard : d8137 p = 1) : d551 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d551, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41707 p hg
    simpa only [d8137, d551, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d551, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41679 p hg
    simpa only [d8137, d551, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41709 (p : Pattern) (guard : d8138 p = 1) : d552 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d552, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41699 p hg
    simpa only [d8138, d552, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d552, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41708 p hg
    simpa only [d8138, d552, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41710 (p : Pattern) (guard : d8137 p = 1) : d553 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d553, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35538 p hg
    simpa only [d8137, d553, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d553, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41682 p hg
    simpa only [d8137, d553, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41711 (p : Pattern) (guard : d8111 p = 1) : d519 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41615 p hg
    simpa only [d8111, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5064 p hg
    simpa only [d8111, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41712 (p : Pattern) (guard : d0 p = 1) : d520 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41713 (p : Pattern) (guard : d8117 p = 1) : d521 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41711 p hg
    simpa only [d8117, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41712 p hg
    simpa only [d8117, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41714 (p : Pattern) (guard : d0 p = 1) : d592 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41715 (p : Pattern) (guard : d8123 p = 1) : d593 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41713 p hg
    simpa only [d8123, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41714 p hg
    simpa only [d8123, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41716 (p : Pattern) (guard : d0 p = 1) : d594 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41717 (p : Pattern) (guard : d8129 p = 1) : d595 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41715 p hg
    simpa only [d8129, d595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41716 p hg
    simpa only [d8129, d595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41718 (p : Pattern) (guard : d8130 p = 1) : d596 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d596, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41477 p hg
    simpa only [d8130, d596, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d596, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41717 p hg
    simpa only [d8130, d596, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41719 (p : Pattern) (guard : d8135 p = 1) : d604 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d604, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41481 p hg
    simpa only [d8135, d604, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d604, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2870 p hg
    simpa only [d8135, d604, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
