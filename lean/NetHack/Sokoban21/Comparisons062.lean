/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons061
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c8680 (pattern : Twelve) (guard : d1867 pattern = 1) : d1228 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1228, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8672 pattern childGuard
    simpa only [d1228, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1228, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8679 pattern childGuard
    simpa only [d1228, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8681 (pattern : Twelve) (guard : d1867 pattern = 1) : d1193 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1193, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8525 pattern childGuard
    simpa only [d1193, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1193, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8664 pattern childGuard
    simpa only [d1193, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8682 (pattern : Twelve) (guard : d1867 pattern = 1) : d1203 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1203, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8528 pattern childGuard
    simpa only [d1203, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1203, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8681 pattern childGuard
    simpa only [d1203, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8683 (pattern : Twelve) (guard : d1867 pattern = 1) : d1204 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1204, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d1204, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1204, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8670 pattern childGuard
    simpa only [d1204, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8684 (pattern : Twelve) (guard : d1867 pattern = 1) : d1218 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1218, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8682 pattern childGuard
    simpa only [d1218, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1218, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8683 pattern childGuard
    simpa only [d1218, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8685 (pattern : Twelve) (guard : d1867 pattern = 1) : d716 pattern ≤ (0 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d716, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8539 pattern childGuard
    simpa only [d716, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d716, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8675 pattern childGuard
    simpa only [d716, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8686 (pattern : Twelve) (guard : d1867 pattern = 1) : d1219 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1219, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8685 pattern childGuard
    simpa only [d1219, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1219, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8678 pattern childGuard
    simpa only [d1219, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8687 (pattern : Twelve) (guard : d1867 pattern = 1) : d1229 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1229, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8684 pattern childGuard
    simpa only [d1229, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1229, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8686 pattern childGuard
    simpa only [d1229, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8688 (pattern : Twelve) (guard : d1867 pattern = 1) : d1237 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8680 pattern childGuard
    simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8687 pattern childGuard
    simpa only [d1237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8689 (pattern : Twelve) (guard : d1867 pattern = 1) : d1185 pattern ≤ (0 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1185, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8663 pattern childGuard
    simpa only [d1185, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1185, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8551 pattern childGuard
    simpa only [d1185, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8690 (pattern : Twelve) (guard : d1867 pattern = 1) : d1194 pattern ≤ (0 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1194, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8515 pattern childGuard
    simpa only [d1194, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1194, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8689 pattern childGuard
    simpa only [d1194, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8691 (pattern : Twelve) (guard : d1867 pattern = 1) : d1205 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1205, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8555 pattern childGuard
    simpa only [d1205, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1205, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8690 pattern childGuard
    simpa only [d1205, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8692 (pattern : Twelve) (guard : d1867 pattern = 1) : d1206 pattern ≤ (0 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1206, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8515 pattern childGuard
    simpa only [d1206, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1206, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8670 pattern childGuard
    simpa only [d1206, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8693 (pattern : Twelve) (guard : d1867 pattern = 1) : d1220 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1220, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8691 pattern childGuard
    simpa only [d1220, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1220, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8692 pattern childGuard
    simpa only [d1220, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8694 (pattern : Twelve) (guard : d1867 pattern = 1) : d644 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d644, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7748 pattern childGuard
    simpa only [d1867, d644, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d644, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8550 pattern childGuard
    simpa only [d1867, d644, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8695 (pattern : Twelve) (guard : d1867 pattern = 1) : d670 pattern ≤ (0 : Int) + d820 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d670, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8694 pattern childGuard
    simpa only [d670, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d670, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d670, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8696 (pattern : Twelve) (guard : d1867 pattern = 1) : d698 pattern ≤ (0 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d698, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8571 pattern childGuard
    simpa only [d698, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d698, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8695 pattern childGuard
    simpa only [d698, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8697 (pattern : Twelve) (guard : d1867 pattern = 1) : d720 pattern ≤ (0 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d720, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8568 pattern childGuard
    simpa only [d720, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d720, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8696 pattern childGuard
    simpa only [d720, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8698 (pattern : Twelve) (guard : d1867 pattern = 1) : d697 pattern ≤ (0 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d697, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8571 pattern childGuard
    simpa only [d697, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d697, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8565 pattern childGuard
    simpa only [d697, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8699 (pattern : Twelve) (guard : d1867 pattern = 1) : d1186 pattern ≤ (0 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1186, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8573 pattern childGuard
    simpa only [d1186, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1186, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3298 pattern childGuard
    simpa only [d1186, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8700 (pattern : Twelve) (guard : d1867 pattern = 1) : d1195 pattern ≤ (0 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1195, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8699 pattern childGuard
    simpa only [d1195, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1195, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3507 pattern childGuard
    simpa only [d1195, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8701 (pattern : Twelve) (guard : d1867 pattern = 1) : d1207 pattern ≤ (0 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1207, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8698 pattern childGuard
    simpa only [d1207, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1207, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8700 pattern childGuard
    simpa only [d1207, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8702 (pattern : Twelve) (guard : d1867 pattern = 1) : d1221 pattern ≤ (0 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1221, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8697 pattern childGuard
    simpa only [d1221, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1221, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8701 pattern childGuard
    simpa only [d1221, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8703 (pattern : Twelve) (guard : d1867 pattern = 1) : d1230 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1230, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8693 pattern childGuard
    simpa only [d1230, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1230, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8702 pattern childGuard
    simpa only [d1230, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8704 (pattern : Twelve) (guard : d1867 pattern = 1) : d1231 pattern ≤ (0 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1231, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8686 pattern childGuard
    simpa only [d1231, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1231, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1231, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8705 (pattern : Twelve) (guard : d1867 pattern = 1) : d1238 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1238, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8703 pattern childGuard
    simpa only [d1238, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1238, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8704 pattern childGuard
    simpa only [d1238, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8706 (pattern : Twelve) (guard : d1867 pattern = 1) : d1241 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1241, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8688 pattern childGuard
    simpa only [d1241, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1241, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8705 pattern childGuard
    simpa only [d1241, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8707 (pattern : Twelve) (guard : d1867 pattern = 1) : d1208 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1208, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d1208, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1208, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8681 pattern childGuard
    simpa only [d1208, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8708 (pattern : Twelve) (guard : d1867 pattern = 1) : d1222 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1222, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8707 pattern childGuard
    simpa only [d1222, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1222, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8683 pattern childGuard
    simpa only [d1222, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8709 (pattern : Twelve) (guard : d1867 pattern = 1) : d1232 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1232, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8708 pattern childGuard
    simpa only [d1232, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1232, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8686 pattern childGuard
    simpa only [d1232, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8710 (pattern : Twelve) (guard : d1867 pattern = 1) : d1209 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1209, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8535 pattern childGuard
    simpa only [d1209, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1209, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8690 pattern childGuard
    simpa only [d1209, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8711 (pattern : Twelve) (guard : d1867 pattern = 1) : d1223 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1223, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8710 pattern childGuard
    simpa only [d1223, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1223, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8692 pattern childGuard
    simpa only [d1223, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8712 (pattern : Twelve) (guard : d1867 pattern = 1) : d1233 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1233, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8711 pattern childGuard
    simpa only [d1233, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1233, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8702 pattern childGuard
    simpa only [d1233, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8713 (pattern : Twelve) (guard : d1867 pattern = 1) : d1239 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1239, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8712 pattern childGuard
    simpa only [d1239, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1239, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8704 pattern childGuard
    simpa only [d1239, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8714 (pattern : Twelve) (guard : d1867 pattern = 1) : d1242 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1242, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8709 pattern childGuard
    simpa only [d1242, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1242, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8713 pattern childGuard
    simpa only [d1242, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8715 (pattern : Twelve) (guard : d1867 pattern = 1) : d1244 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8706 pattern childGuard
    simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8714 pattern childGuard
    simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8716 (pattern : Twelve) (guard : d1867 pattern = 1) : d1245 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8715 pattern childGuard
    simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8714 pattern childGuard
    simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8717 (pattern : Twelve) (guard : d0 pattern = 1) : d157 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8718 (pattern : Twelve) (guard : d1867 pattern = 1) : d157 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7736 pattern childGuard
    simpa only [d1867, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8717 pattern childGuard
    simpa only [d1867, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8719 (pattern : Twelve) (guard : d1867 pattern = 1) : d661 pattern ≤ (0 : Int) + d874 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d661, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d661, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d661, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8718 pattern childGuard
    simpa only [d661, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8720 (pattern : Twelve) (guard : d1867 pattern = 1) : d1183 pattern ≤ (0 : Int) + d875 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1183, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8663 pattern childGuard
    simpa only [d1183, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1183, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8718 pattern childGuard
    simpa only [d1183, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8721 (pattern : Twelve) (guard : d1867 pattern = 1) : d1193 pattern ≤ (0 : Int) + d882 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1193, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8719 pattern childGuard
    simpa only [d1193, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1193, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8720 pattern childGuard
    simpa only [d1193, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8722 (pattern : Twelve) (guard : d1867 pattern = 1) : d1208 pattern ≤ (0 : Int) + d890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1208, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8485 pattern childGuard
    simpa only [d1208, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1208, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8721 pattern childGuard
    simpa only [d1208, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8723 (pattern : Twelve) (guard : d1867 pattern = 1) : d1187 pattern ≤ (0 : Int) + d876 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1187, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8492 pattern childGuard
    simpa only [d1187, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1187, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3298 pattern childGuard
    simpa only [d1187, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8724 (pattern : Twelve) (guard : d1867 pattern = 1) : d1196 pattern ≤ (0 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1196, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8723 pattern childGuard
    simpa only [d1196, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1196, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8574 pattern childGuard
    simpa only [d1196, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8725 (pattern : Twelve) (guard : d1867 pattern = 1) : d1210 pattern ≤ (0 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1210, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d1210, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1210, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8724 pattern childGuard
    simpa only [d1210, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8726 (pattern : Twelve) (guard : d1867 pattern = 1) : d1224 pattern ≤ (0 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1224, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8722 pattern childGuard
    simpa only [d1224, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1224, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8725 pattern childGuard
    simpa only [d1224, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8727 (pattern : Twelve) (guard : d1867 pattern = 1) : d674 pattern ≤ (0 : Int) + d877 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d674, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d674, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d674, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8694 pattern childGuard
    simpa only [d674, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8728 (pattern : Twelve) (guard : d1867 pattern = 1) : d705 pattern ≤ (0 : Int) + d884 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d705, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8727 pattern childGuard
    simpa only [d705, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d705, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8674 pattern childGuard
    simpa only [d705, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8729 (pattern : Twelve) (guard : d1867 pattern = 1) : d731 pattern ≤ (0 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d731, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8539 pattern childGuard
    simpa only [d731, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d731, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8728 pattern childGuard
    simpa only [d731, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8730 (pattern : Twelve) (guard : d1867 pattern = 1) : d1211 pattern ≤ (0 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1211, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8677 pattern childGuard
    simpa only [d1211, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1211, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8724 pattern childGuard
    simpa only [d1211, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8731 (pattern : Twelve) (guard : d1867 pattern = 1) : d1225 pattern ≤ (0 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1225, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8729 pattern childGuard
    simpa only [d1225, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1225, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8730 pattern childGuard
    simpa only [d1225, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8732 (pattern : Twelve) (guard : d1867 pattern = 1) : d1234 pattern ≤ (0 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1234, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8726 pattern childGuard
    simpa only [d1234, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1234, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8731 pattern childGuard
    simpa only [d1234, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8733 (pattern : Twelve) (guard : d1867 pattern = 1) : d1188 pattern ≤ (0 : Int) + d878 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1188, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8663 pattern childGuard
    simpa only [d1188, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1188, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8570 pattern childGuard
    simpa only [d1188, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8734 (pattern : Twelve) (guard : d1867 pattern = 1) : d1197 pattern ≤ (0 : Int) + d885 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1197, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8727 pattern childGuard
    simpa only [d1197, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1197, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8733 pattern childGuard
    simpa only [d1197, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8735 (pattern : Twelve) (guard : d1867 pattern = 1) : d1212 pattern ≤ (0 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1212, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8535 pattern childGuard
    simpa only [d1212, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1212, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8734 pattern childGuard
    simpa only [d1212, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8736 (pattern : Twelve) (guard : d1867 pattern = 1) : d666 pattern ≤ (0 : Int) + d879 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d666, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d666, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d666, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8644 pattern childGuard
    simpa only [d666, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8737 (pattern : Twelve) (guard : d1867 pattern = 1) : d704 pattern ≤ (0 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d704, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8515 pattern childGuard
    simpa only [d704, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d704, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8736 pattern childGuard
    simpa only [d704, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8738 (pattern : Twelve) (guard : d1867 pattern = 1) : d1213 pattern ≤ (0 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1213, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8737 pattern childGuard
    simpa only [d1213, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1213, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8724 pattern childGuard
    simpa only [d1213, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8739 (pattern : Twelve) (guard : d1867 pattern = 1) : d1226 pattern ≤ (0 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1226, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8735 pattern childGuard
    simpa only [d1226, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1226, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8738 pattern childGuard
    simpa only [d1226, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8740 (pattern : Twelve) (guard : d1867 pattern = 1) : d639 pattern ≤ (0 : Int) + d873 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d639, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7911 pattern childGuard
    simpa only [d1867, d639, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d639, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8569 pattern childGuard
    simpa only [d1867, d639, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8741 (pattern : Twelve) (guard : d1867 pattern = 1) : d679 pattern ≤ (0 : Int) + d880 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d679, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8740 pattern childGuard
    simpa only [d679, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d679, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d679, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8742 (pattern : Twelve) (guard : d1867 pattern = 1) : d708 pattern ≤ (0 : Int) + d887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d708, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8653 pattern childGuard
    simpa only [d708, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d708, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8741 pattern childGuard
    simpa only [d708, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8743 (pattern : Twelve) (guard : d1867 pattern = 1) : d1214 pattern ≤ (0 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1214, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8568 pattern childGuard
    simpa only [d1214, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1214, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8742 pattern childGuard
    simpa only [d1214, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8744 (pattern : Twelve) (guard : d1867 pattern = 1) : d676 pattern ≤ (0 : Int) + d881 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d676, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8514 pattern childGuard
    simpa only [d676, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d676, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8641 pattern childGuard
    simpa only [d676, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8745 (pattern : Twelve) (guard : d1867 pattern = 1) : d707 pattern ≤ (0 : Int) + d888 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d707, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8744 pattern childGuard
    simpa only [d707, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d707, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8645 pattern childGuard
    simpa only [d707, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8746 (pattern : Twelve) (guard : d1867 pattern = 1) : d1198 pattern ≤ (0 : Int) + d889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1198, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8574 pattern childGuard
    simpa only [d1198, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1198, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1198, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8747 (pattern : Twelve) (guard : d1867 pattern = 1) : d1215 pattern ≤ (0 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1215, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8745 pattern childGuard
    simpa only [d1215, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1215, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8746 pattern childGuard
    simpa only [d1215, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8748 (pattern : Twelve) (guard : d1867 pattern = 1) : d1227 pattern ≤ (0 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1227, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8743 pattern childGuard
    simpa only [d1227, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1227, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8747 pattern childGuard
    simpa only [d1227, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8749 (pattern : Twelve) (guard : d1867 pattern = 1) : d1235 pattern ≤ (0 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1235, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8739 pattern childGuard
    simpa only [d1235, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1235, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8748 pattern childGuard
    simpa only [d1235, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8750 (pattern : Twelve) (guard : d1867 pattern = 1) : d1236 pattern ≤ (0 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1236, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8731 pattern childGuard
    simpa only [d1236, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1236, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1236, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8751 (pattern : Twelve) (guard : d1867 pattern = 1) : d1240 pattern ≤ (0 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1240, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8749 pattern childGuard
    simpa only [d1240, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1240, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8750 pattern childGuard
    simpa only [d1240, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8752 (pattern : Twelve) (guard : d1867 pattern = 1) : d1243 pattern ≤ (0 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1243, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8732 pattern childGuard
    simpa only [d1243, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1243, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8751 pattern childGuard
    simpa only [d1243, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8753 (pattern : Twelve) (guard : d1867 pattern = 1) : d1246 pattern ≤ (0 : Int) + d907 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1246, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8716 pattern childGuard
    simpa only [d1246, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1246, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8752 pattern childGuard
    simpa only [d1246, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8754 (pattern : Twelve) (guard : d1867 pattern = 1) : d636 pattern ≤ (0 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d636, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7739 pattern childGuard
    simpa only [d1867, d636, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d636, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8717 pattern childGuard
    simpa only [d1867, d636, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8755 (pattern : Twelve) (guard : d1867 pattern = 1) : d1183 pattern ≤ (0 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1183, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8754 pattern childGuard
    simpa only [d1183, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1183, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8718 pattern childGuard
    simpa only [d1183, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8756 (pattern : Twelve) (guard : d1867 pattern = 1) : d1564 pattern ≤ (0 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1564, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8755 pattern childGuard
    simpa only [d1564, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1564, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8718 pattern childGuard
    simpa only [d1564, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8757 (pattern : Twelve) (guard : d1867 pattern = 1) : d1576 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1576, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8668 pattern childGuard
    simpa only [d1576, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1576, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8756 pattern childGuard
    simpa only [d1576, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8758 (pattern : Twelve) (guard : d1867 pattern = 1) : d1577 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1577, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8492 pattern childGuard
    simpa only [d1577, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1577, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1577, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8759 (pattern : Twelve) (guard : d1867 pattern = 1) : d1591 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1591, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8757 pattern childGuard
    simpa only [d1591, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1591, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8758 pattern childGuard
    simpa only [d1591, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8760 (pattern : Twelve) (guard : d1867 pattern = 1) : d644 pattern ≤ (0 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d644, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7748 pattern childGuard
    simpa only [d1867, d644, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d644, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8643 pattern childGuard
    simpa only [d1867, d644, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8761 (pattern : Twelve) (guard : d1867 pattern = 1) : d1184 pattern ≤ (0 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1184, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8754 pattern childGuard
    simpa only [d1184, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1184, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8760 pattern childGuard
    simpa only [d1184, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8762 (pattern : Twelve) (guard : d1867 pattern = 1) : d1557 pattern ≤ (0 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1557, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8718 pattern childGuard
    simpa only [d1557, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1557, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1557, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8763 (pattern : Twelve) (guard : d1867 pattern = 1) : d1565 pattern ≤ (0 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1565, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8761 pattern childGuard
    simpa only [d1565, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1565, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8762 pattern childGuard
    simpa only [d1565, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8764 (pattern : Twelve) (guard : d1867 pattern = 1) : d1578 pattern ≤ (0 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1578, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8677 pattern childGuard
    simpa only [d1578, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1578, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8763 pattern childGuard
    simpa only [d1578, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8765 (pattern : Twelve) (guard : d1867 pattern = 1) : d1566 pattern ≤ (0 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1566, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8669 pattern childGuard
    simpa only [d1566, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1566, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8493 pattern childGuard
    simpa only [d1566, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8766 (pattern : Twelve) (guard : d1867 pattern = 1) : d1579 pattern ≤ (0 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1579, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8765 pattern childGuard
    simpa only [d1579, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1579, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1579, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8767 (pattern : Twelve) (guard : d1867 pattern = 1) : d1592 pattern ≤ (0 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1592, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8764 pattern childGuard
    simpa only [d1592, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1592, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8766 pattern childGuard
    simpa only [d1592, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8768 (pattern : Twelve) (guard : d1867 pattern = 1) : d1600 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1600, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8759 pattern childGuard
    simpa only [d1600, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1600, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8767 pattern childGuard
    simpa only [d1600, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8769 (pattern : Twelve) (guard : d1867 pattern = 1) : d1580 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1580, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d1580, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1580, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8756 pattern childGuard
    simpa only [d1580, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8770 (pattern : Twelve) (guard : d1867 pattern = 1) : d1593 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1593, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8769 pattern childGuard
    simpa only [d1593, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1593, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8758 pattern childGuard
    simpa only [d1593, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8771 (pattern : Twelve) (guard : d1867 pattern = 1) : d1601 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1601, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8770 pattern childGuard
    simpa only [d1601, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1601, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8767 pattern childGuard
    simpa only [d1601, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8772 (pattern : Twelve) (guard : d1867 pattern = 1) : d1607 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8768 pattern childGuard
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8771 pattern childGuard
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8773 (pattern : Twelve) (guard : d1867 pattern = 1) : d1558 pattern ≤ (0 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1558, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8718 pattern childGuard
    simpa only [d1558, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1558, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8644 pattern childGuard
    simpa only [d1558, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8774 (pattern : Twelve) (guard : d1867 pattern = 1) : d1567 pattern ≤ (0 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1567, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8761 pattern childGuard
    simpa only [d1567, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1567, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8773 pattern childGuard
    simpa only [d1567, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8775 (pattern : Twelve) (guard : d1867 pattern = 1) : d1581 pattern ≤ (0 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1581, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8515 pattern childGuard
    simpa only [d1581, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1581, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8774 pattern childGuard
    simpa only [d1581, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8776 (pattern : Twelve) (guard : d1867 pattern = 1) : d1582 pattern ≤ (0 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1582, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8669 pattern childGuard
    simpa only [d1582, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1582, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1582, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8777 (pattern : Twelve) (guard : d1867 pattern = 1) : d1594 pattern ≤ (0 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1594, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8775 pattern childGuard
    simpa only [d1594, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1594, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8776 pattern childGuard
    simpa only [d1594, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8778 (pattern : Twelve) (guard : d1867 pattern = 1) : d21 pattern ≤ (0 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d21, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7834 pattern childGuard
    simpa only [d1867, d21, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d21, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3445 pattern childGuard
    simpa only [d1867, d21, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8779 (pattern : Twelve) (guard : d1867 pattern = 1) : d1186 pattern ≤ (0 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1186, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8760 pattern childGuard
    simpa only [d1186, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1186, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8778 pattern childGuard
    simpa only [d1186, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8780 (pattern : Twelve) (guard : d1867 pattern = 1) : d1568 pattern ≤ (0 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1568, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8779 pattern childGuard
    simpa only [d1568, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1568, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8645 pattern childGuard
    simpa only [d1568, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8781 (pattern : Twelve) (guard : d1867 pattern = 1) : d1583 pattern ≤ (0 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1583, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8698 pattern childGuard
    simpa only [d1583, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1583, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8780 pattern childGuard
    simpa only [d1583, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8782 (pattern : Twelve) (guard : d1867 pattern = 1) : d1569 pattern ≤ (0 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1569, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8699 pattern childGuard
    simpa only [d1569, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1569, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8574 pattern childGuard
    simpa only [d1569, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8783 (pattern : Twelve) (guard : d1867 pattern = 1) : d1584 pattern ≤ (0 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1584, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8782 pattern childGuard
    simpa only [d1584, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1584, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1584, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8784 (pattern : Twelve) (guard : d1867 pattern = 1) : d1595 pattern ≤ (0 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1595, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8781 pattern childGuard
    simpa only [d1595, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1595, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8783 pattern childGuard
    simpa only [d1595, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8785 (pattern : Twelve) (guard : d1867 pattern = 1) : d1602 pattern ≤ (0 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1602, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8777 pattern childGuard
    simpa only [d1602, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1602, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8784 pattern childGuard
    simpa only [d1602, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8786 (pattern : Twelve) (guard : d1867 pattern = 1) : d1603 pattern ≤ (0 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1603, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8767 pattern childGuard
    simpa only [d1603, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1603, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1603, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8787 (pattern : Twelve) (guard : d1867 pattern = 1) : d1608 pattern ≤ (0 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1608, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8785 pattern childGuard
    simpa only [d1608, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1608, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8786 pattern childGuard
    simpa only [d1608, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8788 (pattern : Twelve) (guard : d1867 pattern = 1) : d1610 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1610, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8772 pattern childGuard
    simpa only [d1610, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1610, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8787 pattern childGuard
    simpa only [d1610, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8789 (pattern : Twelve) (guard : d1867 pattern = 1) : d1611 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1611, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8771 pattern childGuard
    simpa only [d1611, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1611, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8787 pattern childGuard
    simpa only [d1611, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8790 (pattern : Twelve) (guard : d1867 pattern = 1) : d1613 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8788 pattern childGuard
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8789 pattern childGuard
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8791 (pattern : Twelve) (guard : d1867 pattern = 1) : d1614 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8790 pattern childGuard
    simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8789 pattern childGuard
    simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8792 (pattern : Twelve) (guard : d0 pattern = 1) : d160 pattern ≤ (0 : Int) + d16 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8793 (pattern : Twelve) (guard : d1867 pattern = 1) : d635 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d635, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7752 pattern childGuard
    simpa only [d1867, d635, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d635, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8792 pattern childGuard
    simpa only [d1867, d635, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8794 (pattern : Twelve) (guard : d1867 pattern = 1) : d1559 pattern ≤ (0 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1559, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8754 pattern childGuard
    simpa only [d1559, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1559, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8793 pattern childGuard
    simpa only [d1559, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8795 (pattern : Twelve) (guard : d1867 pattern = 1) : d1560 pattern ≤ (0 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1560, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8718 pattern childGuard
    simpa only [d1560, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1560, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8793 pattern childGuard
    simpa only [d1560, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8796 (pattern : Twelve) (guard : d1867 pattern = 1) : d1570 pattern ≤ (0 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1570, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8794 pattern childGuard
    simpa only [d1570, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1570, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8795 pattern childGuard
    simpa only [d1570, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8797 (pattern : Twelve) (guard : d1867 pattern = 1) : d1585 pattern ≤ (0 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1585, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8508 pattern childGuard
    simpa only [d1585, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1585, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8796 pattern childGuard
    simpa only [d1585, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8798 (pattern : Twelve) (guard : d1867 pattern = 1) : d1596 pattern ≤ (0 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1596, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8797 pattern childGuard
    simpa only [d1596, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1596, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8758 pattern childGuard
    simpa only [d1596, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8799 (pattern : Twelve) (guard : d1867 pattern = 1) : d1185 pattern ≤ (0 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1185, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8754 pattern childGuard
    simpa only [d1185, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1185, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8644 pattern childGuard
    simpa only [d1185, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8800 (pattern : Twelve) (guard : d1867 pattern = 1) : d1571 pattern ≤ (0 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1571, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8799 pattern childGuard
    simpa only [d1571, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1571, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8762 pattern childGuard
    simpa only [d1571, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8801 (pattern : Twelve) (guard : d1867 pattern = 1) : d1586 pattern ≤ (0 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1586, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8677 pattern childGuard
    simpa only [d1586, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1586, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8800 pattern childGuard
    simpa only [d1586, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8802 (pattern : Twelve) (guard : d1867 pattern = 1) : d1597 pattern ≤ (0 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1597, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8801 pattern childGuard
    simpa only [d1597, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1597, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8766 pattern childGuard
    simpa only [d1597, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8803 (pattern : Twelve) (guard : d1867 pattern = 1) : d1604 pattern ≤ (0 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1604, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8798 pattern childGuard
    simpa only [d1604, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1604, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8802 pattern childGuard
    simpa only [d1604, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8804 (pattern : Twelve) (guard : d1867 pattern = 1) : d1561 pattern ≤ (0 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1561, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8718 pattern childGuard
    simpa only [d1561, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1561, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8778 pattern childGuard
    simpa only [d1561, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8805 (pattern : Twelve) (guard : d1867 pattern = 1) : d1572 pattern ≤ (0 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1572, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8799 pattern childGuard
    simpa only [d1572, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1572, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8804 pattern childGuard
    simpa only [d1572, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8806 (pattern : Twelve) (guard : d1867 pattern = 1) : d1587 pattern ≤ (0 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1587, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8515 pattern childGuard
    simpa only [d1587, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1587, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8805 pattern childGuard
    simpa only [d1587, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8807 (pattern : Twelve) (guard : d1867 pattern = 1) : d1562 pattern ≤ (0 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1562, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8492 pattern childGuard
    simpa only [d1562, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1562, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8503 pattern childGuard
    simpa only [d1562, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8808 (pattern : Twelve) (guard : d1867 pattern = 1) : d1573 pattern ≤ (0 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1573, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8669 pattern childGuard
    simpa only [d1573, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1573, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8807 pattern childGuard
    simpa only [d1573, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8809 (pattern : Twelve) (guard : d1867 pattern = 1) : d1588 pattern ≤ (0 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1588, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8808 pattern childGuard
    simpa only [d1588, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1588, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1588, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8810 (pattern : Twelve) (guard : d1867 pattern = 1) : d1598 pattern ≤ (0 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1598, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8806 pattern childGuard
    simpa only [d1598, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1598, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8809 pattern childGuard
    simpa only [d1598, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8811 (pattern : Twelve) (guard : d1867 pattern = 1) : d670 pattern ≤ (0 : Int) + d1330 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d670, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8760 pattern childGuard
    simpa only [d670, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d670, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d670, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8812 (pattern : Twelve) (guard : d1867 pattern = 1) : d822 pattern ≤ (0 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d822, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8778 pattern childGuard
    simpa only [d822, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d822, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d822, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8813 (pattern : Twelve) (guard : d1867 pattern = 1) : d1574 pattern ≤ (0 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1574, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8811 pattern childGuard
    simpa only [d1574, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1574, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8812 pattern childGuard
    simpa only [d1574, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8814 (pattern : Twelve) (guard : d1867 pattern = 1) : d1589 pattern ≤ (0 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1589, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8698 pattern childGuard
    simpa only [d1589, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1589, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8813 pattern childGuard
    simpa only [d1589, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8815 (pattern : Twelve) (guard : d1867 pattern = 1) : d1563 pattern ≤ (0 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1563, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8573 pattern childGuard
    simpa only [d1563, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1563, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d1563, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8816 (pattern : Twelve) (guard : d1867 pattern = 1) : d1575 pattern ≤ (0 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1575, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8815 pattern childGuard
    simpa only [d1575, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1575, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8654 pattern childGuard
    simpa only [d1575, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8817 (pattern : Twelve) (guard : d1867 pattern = 1) : d1590 pattern ≤ (0 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1590, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8816 pattern childGuard
    simpa only [d1590, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1590, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1590, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8818 (pattern : Twelve) (guard : d1867 pattern = 1) : d1599 pattern ≤ (0 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1599, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8814 pattern childGuard
    simpa only [d1599, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1599, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8817 pattern childGuard
    simpa only [d1599, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8819 (pattern : Twelve) (guard : d1867 pattern = 1) : d1605 pattern ≤ (0 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1605, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8810 pattern childGuard
    simpa only [d1605, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1605, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8818 pattern childGuard
    simpa only [d1605, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
