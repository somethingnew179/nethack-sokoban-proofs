/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons132
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c18620 (pattern : Twelve) (guard : d1 pattern = 1) : d127 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11278 pattern childGuard
    simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11431 pattern childGuard
    simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18621 (pattern : Twelve) (guard : d1 pattern = 1) : d135 pattern ≤ (1 : Int) + d889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18620 pattern childGuard
    simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17612 pattern childGuard
    simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18622 (pattern : Twelve) (guard : d1 pattern = 1) : d143 pattern ≤ (1 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18619 pattern childGuard
    simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18621 pattern childGuard
    simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18623 (pattern : Twelve) (guard : d1 pattern = 1) : d148 pattern ≤ (1 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18615 pattern childGuard
    simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18622 pattern childGuard
    simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18624 (pattern : Twelve) (guard : d1 pattern = 1) : d151 pattern ≤ (1 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18609 pattern childGuard
    simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18623 pattern childGuard
    simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18625 (pattern : Twelve) (guard : d1 pattern = 1) : d152 pattern ≤ (1 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18599 pattern childGuard
    simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18626 (pattern : Twelve) (guard : d1 pattern = 1) : d154 pattern ≤ (1 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18624 pattern childGuard
    simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18625 pattern childGuard
    simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18627 (pattern : Twelve) (guard : d1 pattern = 1) : d155 pattern ≤ (1 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18601 pattern childGuard
    simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18626 pattern childGuard
    simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18628 (pattern : Twelve) (guard : d1 pattern = 1) : d156 pattern ≤ (1 : Int) + d907 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d156, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18582 pattern childGuard
    simpa only [d156, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d156, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18627 pattern childGuard
    simpa only [d156, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18629 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (1 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17542 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18583 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18630 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (1 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12052 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11214 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18631 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (1 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18630 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18583 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18632 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (1 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18629 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18631 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18633 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (1 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18632 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18634 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17556 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11947 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18635 (pattern : Twelve) (guard : d1 pattern = 1) : d839 pattern ≤ (1 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11225 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18634 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18636 (pattern : Twelve) (guard : d1 pattern = 1) : d853 pattern ≤ (1 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18633 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18635 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18637 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (1 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18630 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18638 (pattern : Twelve) (guard : d1 pattern = 1) : d826 pattern ≤ (1 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17551 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18637 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18639 (pattern : Twelve) (guard : d1 pattern = 1) : d840 pattern ≤ (1 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18562 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18638 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18640 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (1 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11225 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18641 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (1 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17453 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18640 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18642 (pattern : Twelve) (guard : d1 pattern = 1) : d841 pattern ≤ (1 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18641 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18634 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18643 (pattern : Twelve) (guard : d1 pattern = 1) : d854 pattern ≤ (1 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18639 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18642 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18644 (pattern : Twelve) (guard : d1 pattern = 1) : d861 pattern ≤ (1 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18636 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18643 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18645 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (1 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18630 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18605 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18646 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (1 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17551 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18645 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18647 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (1 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17334 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18646 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18648 (pattern : Twelve) (guard : d1 pattern = 1) : d843 pattern ≤ (1 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17453 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18634 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18649 (pattern : Twelve) (guard : d1 pattern = 1) : d855 pattern ≤ (1 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18647 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18648 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18650 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (1 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12069 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11268 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18651 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (1 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18650 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18652 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (1 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17570 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18651 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18653 (pattern : Twelve) (guard : d1 pattern = 1) : d844 pattern ≤ (1 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18574 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18652 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18654 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11278 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18655 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17475 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18654 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18656 (pattern : Twelve) (guard : d1 pattern = 1) : d831 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11946 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11956 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18657 (pattern : Twelve) (guard : d1 pattern = 1) : d845 pattern ≤ (1 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18655 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18656 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18658 (pattern : Twelve) (guard : d1 pattern = 1) : d856 pattern ≤ (1 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18653 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18657 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18659 (pattern : Twelve) (guard : d1 pattern = 1) : d862 pattern ≤ (1 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18649 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18658 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18660 (pattern : Twelve) (guard : d1 pattern = 1) : d863 pattern ≤ (1 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18643 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18661 (pattern : Twelve) (guard : d1 pattern = 1) : d867 pattern ≤ (1 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18659 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18660 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18662 (pattern : Twelve) (guard : d1 pattern = 1) : d869 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18644 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18661 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18663 (pattern : Twelve) (guard : d1 pattern = 1) : d874 pattern ≤ (1 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17542 pattern childGuard
    simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11334 pattern childGuard
    simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18664 (pattern : Twelve) (guard : d1 pattern = 1) : d875 pattern ≤ (1 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18630 pattern childGuard
    simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11334 pattern childGuard
    simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18665 (pattern : Twelve) (guard : d1 pattern = 1) : d882 pattern ≤ (1 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18663 pattern childGuard
    simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18664 pattern childGuard
    simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18666 (pattern : Twelve) (guard : d1 pattern = 1) : d890 pattern ≤ (1 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11062 pattern childGuard
    simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18665 pattern childGuard
    simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18667 (pattern : Twelve) (guard : d1 pattern = 1) : d876 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11407 pattern childGuard
    simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11285 pattern childGuard
    simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18668 (pattern : Twelve) (guard : d1 pattern = 1) : d883 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18667 pattern childGuard
    simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11947 pattern childGuard
    simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18669 (pattern : Twelve) (guard : d1 pattern = 1) : d891 pattern ≤ (1 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11225 pattern childGuard
    simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18668 pattern childGuard
    simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18670 (pattern : Twelve) (guard : d1 pattern = 1) : d898 pattern ≤ (1 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18666 pattern childGuard
    simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18669 pattern childGuard
    simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18671 (pattern : Twelve) (guard : d1 pattern = 1) : d877 pattern ≤ (1 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17542 pattern childGuard
    simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18650 pattern childGuard
    simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18672 (pattern : Twelve) (guard : d1 pattern = 1) : d884 pattern ≤ (1 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18671 pattern childGuard
    simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18637 pattern childGuard
    simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18673 (pattern : Twelve) (guard : d1 pattern = 1) : d892 pattern ≤ (1 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18562 pattern childGuard
    simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18672 pattern childGuard
    simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18674 (pattern : Twelve) (guard : d1 pattern = 1) : d893 pattern ≤ (1 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18641 pattern childGuard
    simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18668 pattern childGuard
    simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18675 (pattern : Twelve) (guard : d1 pattern = 1) : d899 pattern ≤ (1 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18673 pattern childGuard
    simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18674 pattern childGuard
    simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18676 (pattern : Twelve) (guard : d1 pattern = 1) : d902 pattern ≤ (1 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18670 pattern childGuard
    simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18675 pattern childGuard
    simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18677 (pattern : Twelve) (guard : d1 pattern = 1) : d878 pattern ≤ (1 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18630 pattern childGuard
    simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17569 pattern childGuard
    simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18678 (pattern : Twelve) (guard : d1 pattern = 1) : d885 pattern ≤ (1 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18671 pattern childGuard
    simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18677 pattern childGuard
    simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18679 (pattern : Twelve) (guard : d1 pattern = 1) : d894 pattern ≤ (1 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17334 pattern childGuard
    simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18678 pattern childGuard
    simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18680 (pattern : Twelve) (guard : d1 pattern = 1) : d879 pattern ≤ (1 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11225 pattern childGuard
    simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11365 pattern childGuard
    simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18681 (pattern : Twelve) (guard : d1 pattern = 1) : d886 pattern ≤ (1 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17453 pattern childGuard
    simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18680 pattern childGuard
    simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18682 (pattern : Twelve) (guard : d1 pattern = 1) : d895 pattern ≤ (1 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18681 pattern childGuard
    simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18668 pattern childGuard
    simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18683 (pattern : Twelve) (guard : d1 pattern = 1) : d900 pattern ≤ (1 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18679 pattern childGuard
    simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18682 pattern childGuard
    simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18684 (pattern : Twelve) (guard : d1 pattern = 1) : d127 pattern ≤ (1 : Int) + d1330 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17550 pattern childGuard
    simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11431 pattern childGuard
    simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18685 (pattern : Twelve) (guard : d1 pattern = 1) : d873 pattern ≤ (1 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12543 pattern childGuard
    simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12584 pattern childGuard
    simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18686 (pattern : Twelve) (guard : d1 pattern = 1) : d880 pattern ≤ (1 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18685 pattern childGuard
    simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18687 (pattern : Twelve) (guard : d1 pattern = 1) : d887 pattern ≤ (1 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18684 pattern childGuard
    simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18686 pattern childGuard
    simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18688 (pattern : Twelve) (guard : d1 pattern = 1) : d896 pattern ≤ (1 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18574 pattern childGuard
    simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18687 pattern childGuard
    simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18689 (pattern : Twelve) (guard : d1 pattern = 1) : d881 pattern ≤ (1 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11278 pattern childGuard
    simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18610 pattern childGuard
    simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18690 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (1 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11365 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18691 (pattern : Twelve) (guard : d1 pattern = 1) : d888 pattern ≤ (1 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18689 pattern childGuard
    simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18690 pattern childGuard
    simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18692 (pattern : Twelve) (guard : d1 pattern = 1) : d889 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11947 pattern childGuard
    simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18693 (pattern : Twelve) (guard : d1 pattern = 1) : d897 pattern ≤ (1 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18691 pattern childGuard
    simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18692 pattern childGuard
    simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18694 (pattern : Twelve) (guard : d1 pattern = 1) : d901 pattern ≤ (1 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18688 pattern childGuard
    simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18693 pattern childGuard
    simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18695 (pattern : Twelve) (guard : d1 pattern = 1) : d903 pattern ≤ (1 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18683 pattern childGuard
    simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18694 pattern childGuard
    simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18696 (pattern : Twelve) (guard : d1 pattern = 1) : d904 pattern ≤ (1 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18675 pattern childGuard
    simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18697 (pattern : Twelve) (guard : d1 pattern = 1) : d905 pattern ≤ (1 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18695 pattern childGuard
    simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18696 pattern childGuard
    simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18698 (pattern : Twelve) (guard : d1 pattern = 1) : d906 pattern ≤ (1 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18676 pattern childGuard
    simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18697 pattern childGuard
    simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18699 (pattern : Twelve) (guard : d1 pattern = 1) : d907 pattern ≤ (1 : Int) + d1354 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d907, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18662 pattern childGuard
    simpa only [d907, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d907, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18698 pattern childGuard
    simpa only [d907, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18700 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11224 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11333 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18701 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18700 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11334 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18702 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18701 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11334 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18703 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (1 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11225 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18702 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18704 (pattern : Twelve) (guard : d1 pattern = 1) : d1294 pattern ≤ (1 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11342 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18705 (pattern : Twelve) (guard : d1 pattern = 1) : d1305 pattern ≤ (1 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18703 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18704 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18706 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (1 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11277 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11364 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18707 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18700 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18706 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18708 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (1 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11334 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18709 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (1 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18707 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18708 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18710 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (1 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18641 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18709 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18711 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11342 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11373 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18712 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18711 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18543 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18713 (pattern : Twelve) (guard : d1 pattern = 1) : d1296 pattern ≤ (1 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18712 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18714 (pattern : Twelve) (guard : d1 pattern = 1) : d1306 pattern ≤ (1 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18710 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18713 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18715 (pattern : Twelve) (guard : d1 pattern = 1) : d1313 pattern ≤ (1 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18705 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18714 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18716 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11334 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11365 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18717 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18707 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18716 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18718 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (1 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17453 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18717 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18719 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (1 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18711 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18720 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (1 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18718 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18719 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18721 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (1 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12584 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11284 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18722 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (1 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18706 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18721 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18723 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (1 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18722 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18690 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18724 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (1 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18655 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18723 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18725 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11373 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11285 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18726 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18725 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18575 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18727 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (1 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18726 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18728 (pattern : Twelve) (guard : d1 pattern = 1) : d1308 pattern ≤ (1 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18724 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18727 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18729 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (1 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18720 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18728 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18730 (pattern : Twelve) (guard : d1 pattern = 1) : d1315 pattern ≤ (1 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18714 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18731 (pattern : Twelve) (guard : d1 pattern = 1) : d1319 pattern ≤ (1 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18729 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18730 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18732 (pattern : Twelve) (guard : d1 pattern = 1) : d1321 pattern ≤ (1 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18715 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18731 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18733 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (1 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11341 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11371 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18734 (pattern : Twelve) (guard : d1 pattern = 1) : d1325 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18700 pattern childGuard
    simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18733 pattern childGuard
    simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18735 (pattern : Twelve) (guard : d1 pattern = 1) : d1326 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11334 pattern childGuard
    simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18733 pattern childGuard
    simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18736 (pattern : Twelve) (guard : d1 pattern = 1) : d1333 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18734 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18735 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18737 (pattern : Twelve) (guard : d1 pattern = 1) : d1339 pattern ≤ (1 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11225 pattern childGuard
    simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18736 pattern childGuard
    simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18738 (pattern : Twelve) (guard : d1 pattern = 1) : d1345 pattern ≤ (1 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18737 pattern childGuard
    simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18704 pattern childGuard
    simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18739 (pattern : Twelve) (guard : d1 pattern = 1) : d1327 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18700 pattern childGuard
    simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11365 pattern childGuard
    simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18740 (pattern : Twelve) (guard : d1 pattern = 1) : d1334 pattern ≤ (1 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18739 pattern childGuard
    simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18708 pattern childGuard
    simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18741 (pattern : Twelve) (guard : d1 pattern = 1) : d1340 pattern ≤ (1 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18641 pattern childGuard
    simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18740 pattern childGuard
    simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18742 (pattern : Twelve) (guard : d1 pattern = 1) : d1346 pattern ≤ (1 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18741 pattern childGuard
    simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18713 pattern childGuard
    simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18743 (pattern : Twelve) (guard : d1 pattern = 1) : d1349 pattern ≤ (1 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18738 pattern childGuard
    simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18742 pattern childGuard
    simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18744 (pattern : Twelve) (guard : d1 pattern = 1) : d1328 pattern ≤ (1 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11334 pattern childGuard
    simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18721 pattern childGuard
    simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18745 (pattern : Twelve) (guard : d1 pattern = 1) : d1335 pattern ≤ (1 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18739 pattern childGuard
    simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18744 pattern childGuard
    simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18746 (pattern : Twelve) (guard : d1 pattern = 1) : d1341 pattern ≤ (1 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17453 pattern childGuard
    simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18745 pattern childGuard
    simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18747 (pattern : Twelve) (guard : d1 pattern = 1) : d1329 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11342 pattern childGuard
    simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11419 pattern childGuard
    simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18748 (pattern : Twelve) (guard : d1 pattern = 1) : d1336 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18711 pattern childGuard
    simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18747 pattern childGuard
    simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18749 (pattern : Twelve) (guard : d1 pattern = 1) : d1342 pattern ≤ (1 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18748 pattern childGuard
    simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1342, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18750 (pattern : Twelve) (guard : d1 pattern = 1) : d1347 pattern ≤ (1 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18746 pattern childGuard
    simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18749 pattern childGuard
    simpa only [d1347, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18751 (pattern : Twelve) (guard : d1 pattern = 1) : d1330 pattern ≤ (1 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18706 pattern childGuard
    simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1330, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18752 (pattern : Twelve) (guard : d1 pattern = 1) : d1331 pattern ≤ (1 : Int) + d183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18721 pattern childGuard
    simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1331, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18753 (pattern : Twelve) (guard : d1 pattern = 1) : d1337 pattern ≤ (1 : Int) + d1667 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18751 pattern childGuard
    simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18752 pattern childGuard
    simpa only [d1337, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18754 (pattern : Twelve) (guard : d1 pattern = 1) : d1343 pattern ≤ (1 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18655 pattern childGuard
    simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18753 pattern childGuard
    simpa only [d1343, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18755 (pattern : Twelve) (guard : d1 pattern = 1) : d1332 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11373 pattern childGuard
    simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11431 pattern childGuard
    simpa only [d1332, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18756 (pattern : Twelve) (guard : d1 pattern = 1) : d1338 pattern ≤ (1 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18755 pattern childGuard
    simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17612 pattern childGuard
    simpa only [d1338, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18757 (pattern : Twelve) (guard : d1 pattern = 1) : d1344 pattern ≤ (1 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18756 pattern childGuard
    simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d1344, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18758 (pattern : Twelve) (guard : d1 pattern = 1) : d1348 pattern ≤ (1 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18754 pattern childGuard
    simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18757 pattern childGuard
    simpa only [d1348, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18759 (pattern : Twelve) (guard : d1 pattern = 1) : d1350 pattern ≤ (1 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18750 pattern childGuard
    simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18758 pattern childGuard
    simpa only [d1350, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
