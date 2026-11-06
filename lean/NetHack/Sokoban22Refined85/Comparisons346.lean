/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons345
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare48440 (p : Pattern) (guard : d8132 p = 1) : d847 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d847, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48436 p hg
    simpa only [d8132, d847, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d847, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48439 p hg
    simpa only [d8132, d847, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48441 (p : Pattern) (guard : d8133 p = 1) : d848 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d848, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48429 p hg
    simpa only [d8133, d848, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d848, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48440 p hg
    simpa only [d8133, d848, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48442 (p : Pattern) (guard : d8113 p = 1) : d403 p ≤ (0 : Int) + d403 p := by
  omega
theorem compare48443 (p : Pattern) (guard : d8114 p = 1) : d815 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d815, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34855 p hg
    simpa only [d8114, d815, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d815, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48442 p hg
    simpa only [d8114, d815, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48444 (p : Pattern) (guard : d8113 p = 1) : d791 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d791, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47842 p hg
    simpa only [d8113, d791, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d791, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34919 p hg
    simpa only [d8113, d791, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48445 (p : Pattern) (guard : d8119 p = 1) : d826 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d826, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48444 p hg
    simpa only [d8119, d826, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d826, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d826, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48446 (p : Pattern) (guard : d8120 p = 1) : d849 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d849, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48443 p hg
    simpa only [d8120, d849, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d849, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48445 p hg
    simpa only [d8120, d849, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48447 (p : Pattern) (guard : d8118 p = 1) : d375 p ≤ (0 : Int) + d375 p := by
  omega
theorem compare48448 (p : Pattern) (guard : d8119 p = 1) : d817 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d817, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34892 p hg
    simpa only [d8119, d817, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d817, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48447 p hg
    simpa only [d8119, d817, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48449 (p : Pattern) (guard : d8111 p = 1) : d797 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d8111, d797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5064 p hg
    simpa only [d8111, d797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48450 (p : Pattern) (guard : d8117 p = 1) : d798 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48449 p hg
    simpa only [d8117, d798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3664 p hg
    simpa only [d8117, d798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48451 (p : Pattern) (guard : d8118 p = 1) : d799 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47852 p hg
    simpa only [d8118, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48450 p hg
    simpa only [d8118, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48452 (p : Pattern) (guard : d8124 p = 1) : d800 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48451 p hg
    simpa only [d8124, d800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48453 (p : Pattern) (guard : d8125 p = 1) : d850 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d850, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48448 p hg
    simpa only [d8125, d850, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d850, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48452 p hg
    simpa only [d8125, d850, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48454 (p : Pattern) (guard : d8126 p = 1) : d851 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d851, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48446 p hg
    simpa only [d8126, d851, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d851, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48453 p hg
    simpa only [d8126, d851, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48455 (p : Pattern) (guard : d8119 p = 1) : d831 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d831, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d8119, d831, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d831, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d831, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48456 (p : Pattern) (guard : d8118 p = 1) : d804 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47861 p hg
    simpa only [d8118, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35545 p hg
    simpa only [d8118, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48457 (p : Pattern) (guard : d8124 p = 1) : d805 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48456 p hg
    simpa only [d8124, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48458 (p : Pattern) (guard : d8125 p = 1) : d832 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d832, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48455 p hg
    simpa only [d8125, d832, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d832, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48457 p hg
    simpa only [d8125, d832, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48459 (p : Pattern) (guard : d8124 p = 1) : d807 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d807, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34932 p hg
    simpa only [d8124, d807, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d807, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d807, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48460 (p : Pattern) (guard : d8123 p = 1) : d810 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47867 p hg
    simpa only [d8123, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6431 p hg
    simpa only [d8123, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48461 (p : Pattern) (guard : d8129 p = 1) : d811 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48460 p hg
    simpa only [d8129, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48462 (p : Pattern) (guard : d8130 p = 1) : d812 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d812, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48459 p hg
    simpa only [d8130, d812, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d812, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48461 p hg
    simpa only [d8130, d812, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48463 (p : Pattern) (guard : d8131 p = 1) : d833 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d833, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48458 p hg
    simpa only [d8131, d833, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d833, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48462 p hg
    simpa only [d8131, d833, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48464 (p : Pattern) (guard : d8132 p = 1) : d852 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d852, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48454 p hg
    simpa only [d8132, d852, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d852, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48463 p hg
    simpa only [d8132, d852, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48465 (p : Pattern) (guard : d8119 p = 1) : d831 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d831, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35066 p hg
    simpa only [d8119, d831, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d831, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d831, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48466 (p : Pattern) (guard : d8125 p = 1) : d832 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d832, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48465 p hg
    simpa only [d8125, d832, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d832, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48457 p hg
    simpa only [d8125, d832, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48467 (p : Pattern) (guard : d8124 p = 1) : d807 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d807, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35075 p hg
    simpa only [d8124, d807, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d807, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d807, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48468 (p : Pattern) (guard : d8130 p = 1) : d812 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d812, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48467 p hg
    simpa only [d8130, d812, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d812, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48461 p hg
    simpa only [d8130, d812, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48469 (p : Pattern) (guard : d8131 p = 1) : d833 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d833, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48466 p hg
    simpa only [d8131, d833, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d833, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48468 p hg
    simpa only [d8131, d833, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48470 (p : Pattern) (guard : d8137 p = 1) : d835 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d835, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48469 p hg
    simpa only [d8137, d835, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d835, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d835, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48471 (p : Pattern) (guard : d8138 p = 1) : d853 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d853, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48464 p hg
    simpa only [d8138, d853, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d853, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48470 p hg
    simpa only [d8138, d853, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48472 (p : Pattern) (guard : d8139 p = 1) : d854 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d854, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48441 p hg
    simpa only [d8139, d854, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d854, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48471 p hg
    simpa only [d8139, d854, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48473 (p : Pattern) (guard : d8140 p = 1) : d855 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d855, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48412 p hg
    simpa only [d8140, d855, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d855, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48472 p hg
    simpa only [d8140, d855, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48474 (p : Pattern) (guard : d8108 p = 1) : d362 p ≤ (0 : Int) + d362 p := by
  omega
theorem compare48475 (p : Pattern) (guard : d8109 p = 1) : d790 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d790, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34951 p hg
    simpa only [d8109, d790, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d790, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48474 p hg
    simpa only [d8109, d790, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48476 (p : Pattern) (guard : d8108 p = 1) : d791 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d791, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47889 p hg
    simpa only [d8108, d791, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d791, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38172 p hg
    simpa only [d8108, d791, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48477 (p : Pattern) (guard : d8114 p = 1) : d792 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d792, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48476 p hg
    simpa only [d8114, d792, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d792, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48372 p hg
    simpa only [d8114, d792, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48478 (p : Pattern) (guard : d8115 p = 1) : d793 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d793, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48475 p hg
    simpa only [d8115, d793, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d793, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48477 p hg
    simpa only [d8115, d793, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48479 (p : Pattern) (guard : d8113 p = 1) : d387 p ≤ (0 : Int) + d387 p := by
  omega
theorem compare48480 (p : Pattern) (guard : d8114 p = 1) : d794 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d794, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34984 p hg
    simpa only [d8114, d794, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d794, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48479 p hg
    simpa only [d8114, d794, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48481 (p : Pattern) (guard : d8113 p = 1) : d799 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d799, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47808 p hg
    simpa only [d8113, d799, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d799, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48389 p hg
    simpa only [d8113, d799, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48482 (p : Pattern) (guard : d8119 p = 1) : d800 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d800, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48481 p hg
    simpa only [d8119, d800, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d800, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d800, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48483 (p : Pattern) (guard : d8120 p = 1) : d801 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d801, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48480 p hg
    simpa only [d8120, d801, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d801, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48482 p hg
    simpa only [d8120, d801, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48484 (p : Pattern) (guard : d8121 p = 1) : d802 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d802, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48478 p hg
    simpa only [d8121, d802, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d802, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48483 p hg
    simpa only [d8121, d802, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48485 (p : Pattern) (guard : d8127 p = 1) : d814 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d814, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48484 p hg
    simpa only [d8127, d814, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d814, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48436 p hg
    simpa only [d8127, d814, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48486 (p : Pattern) (guard : d8113 p = 1) : d804 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d804, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47907 p hg
    simpa only [d8113, d804, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d804, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34919 p hg
    simpa only [d8113, d804, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48487 (p : Pattern) (guard : d8119 p = 1) : d805 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d805, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48486 p hg
    simpa only [d8119, d805, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d805, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d805, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48488 (p : Pattern) (guard : d8120 p = 1) : d816 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d816, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48443 p hg
    simpa only [d8120, d816, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d816, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48487 p hg
    simpa only [d8120, d816, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48489 (p : Pattern) (guard : d8125 p = 1) : d818 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d818, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48448 p hg
    simpa only [d8125, d818, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d818, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48401 p hg
    simpa only [d8125, d818, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48490 (p : Pattern) (guard : d8126 p = 1) : d819 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d819, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48488 p hg
    simpa only [d8126, d819, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d819, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48489 p hg
    simpa only [d8126, d819, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48491 (p : Pattern) (guard : d8119 p = 1) : d820 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d820, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38178 p hg
    simpa only [d8119, d820, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d820, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d820, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48492 (p : Pattern) (guard : d8125 p = 1) : d821 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d821, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48491 p hg
    simpa only [d8125, d821, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d821, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38152 p hg
    simpa only [d8125, d821, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48493 (p : Pattern) (guard : d8131 p = 1) : d822 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d822, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48492 p hg
    simpa only [d8131, d822, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d822, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41412 p hg
    simpa only [d8131, d822, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48494 (p : Pattern) (guard : d8132 p = 1) : d823 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d823, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48490 p hg
    simpa only [d8132, d823, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d823, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48493 p hg
    simpa only [d8132, d823, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48495 (p : Pattern) (guard : d8133 p = 1) : d824 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d824, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48485 p hg
    simpa only [d8133, d824, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d824, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48494 p hg
    simpa only [d8133, d824, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48496 (p : Pattern) (guard : d8114 p = 1) : d825 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d825, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d8114, d825, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d825, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48418 p hg
    simpa only [d8114, d825, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48497 (p : Pattern) (guard : d8113 p = 1) : d791 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d791, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47922 p hg
    simpa only [d8113, d791, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d791, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34919 p hg
    simpa only [d8113, d791, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48498 (p : Pattern) (guard : d8119 p = 1) : d826 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d826, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48497 p hg
    simpa only [d8119, d826, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d826, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d826, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48499 (p : Pattern) (guard : d8120 p = 1) : d827 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d827, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48496 p hg
    simpa only [d8120, d827, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d827, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48498 p hg
    simpa only [d8120, d827, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48500 (p : Pattern) (guard : d8118 p = 1) : d394 p ≤ (0 : Int) + d394 p := by
  omega
theorem compare48501 (p : Pattern) (guard : d8119 p = 1) : d828 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d828, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35055 p hg
    simpa only [d8119, d828, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d828, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48500 p hg
    simpa only [d8119, d828, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48502 (p : Pattern) (guard : d8118 p = 1) : d799 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d799, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47849 p hg
    simpa only [d8118, d799, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d799, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48450 p hg
    simpa only [d8118, d799, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48503 (p : Pattern) (guard : d8124 p = 1) : d800 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d800, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48502 p hg
    simpa only [d8124, d800, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d800, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d800, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48504 (p : Pattern) (guard : d8125 p = 1) : d829 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d829, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48501 p hg
    simpa only [d8125, d829, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d829, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48503 p hg
    simpa only [d8125, d829, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48505 (p : Pattern) (guard : d8126 p = 1) : d830 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d830, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48499 p hg
    simpa only [d8126, d830, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d830, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48504 p hg
    simpa only [d8126, d830, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48506 (p : Pattern) (guard : d8132 p = 1) : d834 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d834, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48505 p hg
    simpa only [d8132, d834, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d834, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48469 p hg
    simpa only [d8132, d834, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48507 (p : Pattern) (guard : d8119 p = 1) : d831 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d831, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38188 p hg
    simpa only [d8119, d831, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d831, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d831, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48508 (p : Pattern) (guard : d8125 p = 1) : d832 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d832, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48507 p hg
    simpa only [d8125, d832, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d832, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48457 p hg
    simpa only [d8125, d832, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48509 (p : Pattern) (guard : d8124 p = 1) : d807 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d807, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41417 p hg
    simpa only [d8124, d807, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d807, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d807, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48510 (p : Pattern) (guard : d8130 p = 1) : d812 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d812, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48509 p hg
    simpa only [d8130, d812, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d812, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48461 p hg
    simpa only [d8130, d812, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48511 (p : Pattern) (guard : d8131 p = 1) : d833 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d833, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48508 p hg
    simpa only [d8131, d833, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d833, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48510 p hg
    simpa only [d8131, d833, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48512 (p : Pattern) (guard : d8137 p = 1) : d835 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d835, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48511 p hg
    simpa only [d8137, d835, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d835, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d835, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48513 (p : Pattern) (guard : d8138 p = 1) : d836 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d836, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48506 p hg
    simpa only [d8138, d836, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d836, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48512 p hg
    simpa only [d8138, d836, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48514 (p : Pattern) (guard : d8139 p = 1) : d837 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d837, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48495 p hg
    simpa only [d8139, d837, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d837, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48513 p hg
    simpa only [d8139, d837, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48515 (p : Pattern) (guard : d8113 p = 1) : d372 p ≤ (0 : Int) + d372 p := by
  omega
theorem compare48516 (p : Pattern) (guard : d8114 p = 1) : d856 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d856, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35142 p hg
    simpa only [d8114, d856, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d856, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48515 p hg
    simpa only [d8114, d856, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48517 (p : Pattern) (guard : d8113 p = 1) : d857 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d857, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47949 p hg
    simpa only [d8113, d857, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d857, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38211 p hg
    simpa only [d8113, d857, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48518 (p : Pattern) (guard : d8119 p = 1) : d858 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d858, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48517 p hg
    simpa only [d8119, d858, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d858, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d858, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48519 (p : Pattern) (guard : d8120 p = 1) : d859 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d859, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48516 p hg
    simpa only [d8120, d859, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d859, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48518 p hg
    simpa only [d8120, d859, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48520 (p : Pattern) (guard : d8118 p = 1) : d390 p ≤ (0 : Int) + d390 p := by
  omega
theorem compare48521 (p : Pattern) (guard : d8119 p = 1) : d860 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d860, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35228 p hg
    simpa only [d8119, d860, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d860, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48520 p hg
    simpa only [d8119, d860, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48522 (p : Pattern) (guard : d8111 p = 1) : d234 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35189 p hg
    simpa only [d8111, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5173 p hg
    simpa only [d8111, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48523 (p : Pattern) (guard : d8117 p = 1) : d863 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48522 p hg
    simpa only [d8117, d863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48524 (p : Pattern) (guard : d8118 p = 1) : d864 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d864, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47980 p hg
    simpa only [d8118, d864, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d864, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48523 p hg
    simpa only [d8118, d864, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48525 (p : Pattern) (guard : d8124 p = 1) : d865 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d865, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48524 p hg
    simpa only [d8124, d865, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d865, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d865, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48526 (p : Pattern) (guard : d8125 p = 1) : d866 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d866, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48521 p hg
    simpa only [d8125, d866, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d866, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48525 p hg
    simpa only [d8125, d866, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48527 (p : Pattern) (guard : d8126 p = 1) : d867 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d867, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48519 p hg
    simpa only [d8126, d867, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d867, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48526 p hg
    simpa only [d8126, d867, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48528 (p : Pattern) (guard : d8119 p = 1) : d868 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d868, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35258 p hg
    simpa only [d8119, d868, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d868, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48447 p hg
    simpa only [d8119, d868, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48529 (p : Pattern) (guard : d8118 p = 1) : d869 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47989 p hg
    simpa only [d8118, d869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35361 p hg
    simpa only [d8118, d869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48530 (p : Pattern) (guard : d8124 p = 1) : d870 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48529 p hg
    simpa only [d8124, d870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48531 (p : Pattern) (guard : d8125 p = 1) : d871 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d871, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48528 p hg
    simpa only [d8125, d871, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d871, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48530 p hg
    simpa only [d8125, d871, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48532 (p : Pattern) (guard : d8124 p = 1) : d872 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d872, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35286 p hg
    simpa only [d8124, d872, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d872, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d872, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48533 (p : Pattern) (guard : d8123 p = 1) : d874 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47995 p hg
    simpa only [d8123, d874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6553 p hg
    simpa only [d8123, d874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48534 (p : Pattern) (guard : d8129 p = 1) : d875 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48533 p hg
    simpa only [d8129, d875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48535 (p : Pattern) (guard : d8130 p = 1) : d876 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d876, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48532 p hg
    simpa only [d8130, d876, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d876, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48534 p hg
    simpa only [d8130, d876, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48536 (p : Pattern) (guard : d8131 p = 1) : d877 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d877, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48531 p hg
    simpa only [d8131, d877, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d877, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48535 p hg
    simpa only [d8131, d877, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48537 (p : Pattern) (guard : d8132 p = 1) : d878 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d878, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48527 p hg
    simpa only [d8132, d878, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d878, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48536 p hg
    simpa only [d8132, d878, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48538 (p : Pattern) (guard : d8119 p = 1) : d879 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d879, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38202 p hg
    simpa only [d8119, d879, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d879, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48500 p hg
    simpa only [d8119, d879, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48539 (p : Pattern) (guard : d8118 p = 1) : d869 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d869, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48005 p hg
    simpa only [d8118, d869, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d869, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35361 p hg
    simpa only [d8118, d869, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48540 (p : Pattern) (guard : d8124 p = 1) : d870 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d870, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48539 p hg
    simpa only [d8124, d870, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d870, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d870, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48541 (p : Pattern) (guard : d8125 p = 1) : d880 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d880, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48538 p hg
    simpa only [d8125, d880, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d880, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48540 p hg
    simpa only [d8125, d880, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48542 (p : Pattern) (guard : d8124 p = 1) : d872 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d872, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41428 p hg
    simpa only [d8124, d872, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d872, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d872, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48543 (p : Pattern) (guard : d8130 p = 1) : d876 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d876, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48542 p hg
    simpa only [d8130, d876, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d876, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48534 p hg
    simpa only [d8130, d876, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48544 (p : Pattern) (guard : d8131 p = 1) : d881 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d881, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48541 p hg
    simpa only [d8131, d881, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d881, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48543 p hg
    simpa only [d8131, d881, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48545 (p : Pattern) (guard : d8137 p = 1) : d882 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d882, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48544 p hg
    simpa only [d8137, d882, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d882, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38220 p hg
    simpa only [d8137, d882, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48546 (p : Pattern) (guard : d8138 p = 1) : d883 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d883, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48537 p hg
    simpa only [d8138, d883, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d883, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48545 p hg
    simpa only [d8138, d883, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48547 (p : Pattern) (guard : d8118 p = 1) : d403 p ≤ (0 : Int) + d403 p := by
  omega
theorem compare48548 (p : Pattern) (guard : d8119 p = 1) : d884 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d884, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35311 p hg
    simpa only [d8119, d884, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d884, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48547 p hg
    simpa only [d8119, d884, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48549 (p : Pattern) (guard : d8118 p = 1) : d857 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d857, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48020 p hg
    simpa only [d8118, d857, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d857, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35361 p hg
    simpa only [d8118, d857, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48550 (p : Pattern) (guard : d8124 p = 1) : d858 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d858, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48549 p hg
    simpa only [d8124, d858, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d858, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d858, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48551 (p : Pattern) (guard : d8125 p = 1) : d885 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d885, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48548 p hg
    simpa only [d8125, d885, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d885, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48550 p hg
    simpa only [d8125, d885, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48552 (p : Pattern) (guard : d8123 p = 1) : d375 p ≤ (0 : Int) + d375 p := by
  omega
theorem compare48553 (p : Pattern) (guard : d8124 p = 1) : d886 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d886, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35344 p hg
    simpa only [d8124, d886, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d886, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48552 p hg
    simpa only [d8124, d886, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48554 (p : Pattern) (guard : d8123 p = 1) : d864 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48029 p hg
    simpa only [d8123, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6535 p hg
    simpa only [d8123, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48555 (p : Pattern) (guard : d8129 p = 1) : d865 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48554 p hg
    simpa only [d8129, d865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48556 (p : Pattern) (guard : d8130 p = 1) : d887 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d887, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48553 p hg
    simpa only [d8130, d887, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d887, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48555 p hg
    simpa only [d8130, d887, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48557 (p : Pattern) (guard : d8131 p = 1) : d888 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d888, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48551 p hg
    simpa only [d8131, d888, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d888, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48556 p hg
    simpa only [d8131, d888, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48558 (p : Pattern) (guard : d8124 p = 1) : d889 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d889, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35357 p hg
    simpa only [d8124, d889, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d889, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d889, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48559 (p : Pattern) (guard : d8123 p = 1) : d869 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48037 p hg
    simpa only [d8123, d869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6544 p hg
    simpa only [d8123, d869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48560 (p : Pattern) (guard : d8129 p = 1) : d870 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48559 p hg
    simpa only [d8129, d870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48561 (p : Pattern) (guard : d8130 p = 1) : d890 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d890, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48558 p hg
    simpa only [d8130, d890, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d890, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48560 p hg
    simpa only [d8130, d890, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48562 (p : Pattern) (guard : d8129 p = 1) : d872 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d872, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35372 p hg
    simpa only [d8129, d872, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d872, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d872, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48563 (p : Pattern) (guard : d8135 p = 1) : d876 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d876, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48562 p hg
    simpa only [d8135, d876, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d876, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7039 p hg
    simpa only [d8135, d876, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48564 (p : Pattern) (guard : d8136 p = 1) : d891 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d891, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48561 p hg
    simpa only [d8136, d891, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d891, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48563 p hg
    simpa only [d8136, d891, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48565 (p : Pattern) (guard : d8137 p = 1) : d892 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d892, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48557 p hg
    simpa only [d8137, d892, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d892, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48564 p hg
    simpa only [d8137, d892, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48566 (p : Pattern) (guard : d8124 p = 1) : d889 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d889, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38229 p hg
    simpa only [d8124, d889, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d889, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d889, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48567 (p : Pattern) (guard : d8130 p = 1) : d890 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d890, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48566 p hg
    simpa only [d8130, d890, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d890, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48560 p hg
    simpa only [d8130, d890, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48568 (p : Pattern) (guard : d8129 p = 1) : d872 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d872, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41435 p hg
    simpa only [d8129, d872, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d872, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d872, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48569 (p : Pattern) (guard : d8135 p = 1) : d876 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d876, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48568 p hg
    simpa only [d8135, d876, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d876, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7039 p hg
    simpa only [d8135, d876, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48570 (p : Pattern) (guard : d8136 p = 1) : d891 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d891, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48567 p hg
    simpa only [d8136, d891, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d891, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48569 p hg
    simpa only [d8136, d891, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48571 (p : Pattern) (guard : d8142 p = 1) : d893 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d893, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48570 p hg
    simpa only [d8142, d893, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d893, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d893, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48572 (p : Pattern) (guard : d8143 p = 1) : d894 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d894, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48565 p hg
    simpa only [d8143, d894, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d894, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48571 p hg
    simpa only [d8143, d894, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48573 (p : Pattern) (guard : d8144 p = 1) : d895 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d895, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48546 p hg
    simpa only [d8144, d895, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d895, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48572 p hg
    simpa only [d8144, d895, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48574 (p : Pattern) (guard : d8145 p = 1) : d896 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d896, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48514 p hg
    simpa only [d8145, d896, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d896, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48573 p hg
    simpa only [d8145, d896, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48575 (p : Pattern) (guard : d8146 p = 1) : d897 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48473 p hg
    simpa only [d8146, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48574 p hg
    simpa only [d8146, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48576 (p : Pattern) (guard : d8114 p = 1) : d838 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d838, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35398 p hg
    simpa only [d8114, d838, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d838, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48515 p hg
    simpa only [d8114, d838, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48577 (p : Pattern) (guard : d8113 p = 1) : d791 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d791, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d8113, d791, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d791, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35620 p hg
    simpa only [d8113, d791, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48578 (p : Pattern) (guard : d8119 p = 1) : d826 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d826, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48577 p hg
    simpa only [d8119, d826, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d826, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d826, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48579 (p : Pattern) (guard : d8120 p = 1) : d839 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d839, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48576 p hg
    simpa only [d8120, d839, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d839, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48578 p hg
    simpa only [d8120, d839, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
