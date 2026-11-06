/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons027
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c3920 (pattern : Twelve) (guard : d1866 pattern = 1) : d894 pattern ≤ (0 : Int) + d1212 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d894, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3730 pattern childGuard
    simpa only [d894, d1212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d894, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3919 pattern childGuard
    simpa only [d894, d1212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3921 (pattern : Twelve) (guard : d1866 pattern = 1) : d879 pattern ≤ (0 : Int) + d666 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d879, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d879, d666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d879, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3831 pattern childGuard
    simpa only [d879, d666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3922 (pattern : Twelve) (guard : d1866 pattern = 1) : d886 pattern ≤ (0 : Int) + d704 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d886, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3710 pattern childGuard
    simpa only [d886, d704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d886, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3921 pattern childGuard
    simpa only [d886, d704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3923 (pattern : Twelve) (guard : d1866 pattern = 1) : d895 pattern ≤ (0 : Int) + d1213 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d895, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3922 pattern childGuard
    simpa only [d895, d1213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d895, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3909 pattern childGuard
    simpa only [d895, d1213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3924 (pattern : Twelve) (guard : d1866 pattern = 1) : d900 pattern ≤ (0 : Int) + d1226 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d900, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3920 pattern childGuard
    simpa only [d900, d1226, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d900, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3923 pattern childGuard
    simpa only [d900, d1226, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3925 (pattern : Twelve) (guard : d1866 pattern = 1) : d873 pattern ≤ (0 : Int) + d639 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d873, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3548 pattern childGuard
    simpa only [d873, d639, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d873, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3587 pattern childGuard
    simpa only [d873, d639, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3926 (pattern : Twelve) (guard : d1866 pattern = 1) : d880 pattern ≤ (0 : Int) + d679 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d880, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3925 pattern childGuard
    simpa only [d880, d679, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d880, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d880, d679, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3927 (pattern : Twelve) (guard : d1866 pattern = 1) : d887 pattern ≤ (0 : Int) + d708 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d887, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3838 pattern childGuard
    simpa only [d887, d708, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d887, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3926 pattern childGuard
    simpa only [d887, d708, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3928 (pattern : Twelve) (guard : d1866 pattern = 1) : d896 pattern ≤ (0 : Int) + d1214 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d896, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3757 pattern childGuard
    simpa only [d896, d1214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d896, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3927 pattern childGuard
    simpa only [d896, d1214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3929 (pattern : Twelve) (guard : d1866 pattern = 1) : d881 pattern ≤ (0 : Int) + d676 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d881, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3709 pattern childGuard
    simpa only [d881, d676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d881, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3829 pattern childGuard
    simpa only [d881, d676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3930 (pattern : Twelve) (guard : d1866 pattern = 1) : d888 pattern ≤ (0 : Int) + d707 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d888, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3929 pattern childGuard
    simpa only [d888, d707, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d888, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3832 pattern childGuard
    simpa only [d888, d707, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3931 (pattern : Twelve) (guard : d1866 pattern = 1) : d889 pattern ≤ (0 : Int) + d1198 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d889, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3761 pattern childGuard
    simpa only [d889, d1198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d889, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d889, d1198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3932 (pattern : Twelve) (guard : d1866 pattern = 1) : d897 pattern ≤ (0 : Int) + d1215 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d897, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3930 pattern childGuard
    simpa only [d897, d1215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d897, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3931 pattern childGuard
    simpa only [d897, d1215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3933 (pattern : Twelve) (guard : d1866 pattern = 1) : d901 pattern ≤ (0 : Int) + d1227 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d901, d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3928 pattern childGuard
    simpa only [d901, d1227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d901, d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3932 pattern childGuard
    simpa only [d901, d1227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3934 (pattern : Twelve) (guard : d1866 pattern = 1) : d903 pattern ≤ (0 : Int) + d1235 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d903, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3924 pattern childGuard
    simpa only [d903, d1235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d903, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3933 pattern childGuard
    simpa only [d903, d1235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3935 (pattern : Twelve) (guard : d1866 pattern = 1) : d904 pattern ≤ (0 : Int) + d1236 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d904, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3916 pattern childGuard
    simpa only [d904, d1236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d904, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d904, d1236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3936 (pattern : Twelve) (guard : d1866 pattern = 1) : d905 pattern ≤ (0 : Int) + d1240 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d905, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3934 pattern childGuard
    simpa only [d905, d1240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d905, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3935 pattern childGuard
    simpa only [d905, d1240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3937 (pattern : Twelve) (guard : d1866 pattern = 1) : d906 pattern ≤ (0 : Int) + d1243 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d906, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3917 pattern childGuard
    simpa only [d906, d1243, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d906, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3936 pattern childGuard
    simpa only [d906, d1243, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3938 (pattern : Twelve) (guard : d1866 pattern = 1) : d907 pattern ≤ (0 : Int) + d1246 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d907, d1246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3902 pattern childGuard
    simpa only [d907, d1246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d907, d1246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3937 pattern childGuard
    simpa only [d907, d1246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3939 (pattern : Twelve) (guard : d1866 pattern = 1) : d1275 pattern ≤ (0 : Int) + d636 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1275, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3468 pattern childGuard
    simpa only [d1275, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1275, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3268 pattern childGuard
    simpa only [d1275, d636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3940 (pattern : Twelve) (guard : d1866 pattern = 1) : d1278 pattern ≤ (0 : Int) + d1183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1278, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3939 pattern childGuard
    simpa only [d1278, d1183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1278, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3903 pattern childGuard
    simpa only [d1278, d1183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3941 (pattern : Twelve) (guard : d1866 pattern = 1) : d1284 pattern ≤ (0 : Int) + d1564 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1284, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3940 pattern childGuard
    simpa only [d1284, d1564, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1284, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3903 pattern childGuard
    simpa only [d1284, d1564, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3942 (pattern : Twelve) (guard : d1866 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1576 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1293, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3853 pattern childGuard
    simpa only [d1293, d1576, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1293, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3941 pattern childGuard
    simpa only [d1293, d1576, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3943 (pattern : Twelve) (guard : d1866 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1577 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1294, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3687 pattern childGuard
    simpa only [d1294, d1577, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1294, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1294, d1577, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3944 (pattern : Twelve) (guard : d1866 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1591 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1305, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3942 pattern childGuard
    simpa only [d1305, d1591, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1305, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3943 pattern childGuard
    simpa only [d1305, d1591, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3945 (pattern : Twelve) (guard : d1866 pattern = 1) : d1276 pattern ≤ (0 : Int) + d644 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1276, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3500 pattern childGuard
    simpa only [d1276, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1276, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3548 pattern childGuard
    simpa only [d1276, d644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3946 (pattern : Twelve) (guard : d1866 pattern = 1) : d1279 pattern ≤ (0 : Int) + d1184 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1279, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3939 pattern childGuard
    simpa only [d1279, d1184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1279, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3945 pattern childGuard
    simpa only [d1279, d1184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3947 (pattern : Twelve) (guard : d1866 pattern = 1) : d1280 pattern ≤ (0 : Int) + d1557 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1280, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3903 pattern childGuard
    simpa only [d1280, d1557, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1280, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1280, d1557, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3948 (pattern : Twelve) (guard : d1866 pattern = 1) : d1285 pattern ≤ (0 : Int) + d1565 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1285, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3946 pattern childGuard
    simpa only [d1285, d1565, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1285, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3947 pattern childGuard
    simpa only [d1285, d1565, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3949 (pattern : Twelve) (guard : d1866 pattern = 1) : d1295 pattern ≤ (0 : Int) + d1578 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1295, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3862 pattern childGuard
    simpa only [d1295, d1578, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1295, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3948 pattern childGuard
    simpa only [d1295, d1578, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3950 (pattern : Twelve) (guard : d1866 pattern = 1) : d1286 pattern ≤ (0 : Int) + d1566 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1286, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3854 pattern childGuard
    simpa only [d1286, d1566, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1286, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3689 pattern childGuard
    simpa only [d1286, d1566, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3951 (pattern : Twelve) (guard : d1866 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1579 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1296, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3950 pattern childGuard
    simpa only [d1296, d1579, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1296, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1296, d1579, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3952 (pattern : Twelve) (guard : d1866 pattern = 1) : d1306 pattern ≤ (0 : Int) + d1592 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1306, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3949 pattern childGuard
    simpa only [d1306, d1592, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1306, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3951 pattern childGuard
    simpa only [d1306, d1592, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3953 (pattern : Twelve) (guard : d1866 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1600 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1313, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3944 pattern childGuard
    simpa only [d1313, d1600, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1313, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3952 pattern childGuard
    simpa only [d1313, d1600, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3954 (pattern : Twelve) (guard : d1866 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1580 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1293, d1580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d1293, d1580, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1293, d1580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3941 pattern childGuard
    simpa only [d1293, d1580, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3955 (pattern : Twelve) (guard : d1866 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1593 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1305, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3954 pattern childGuard
    simpa only [d1305, d1593, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1305, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3943 pattern childGuard
    simpa only [d1305, d1593, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3956 (pattern : Twelve) (guard : d1866 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1601 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1313, d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3955 pattern childGuard
    simpa only [d1313, d1601, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1313, d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3952 pattern childGuard
    simpa only [d1313, d1601, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3957 (pattern : Twelve) (guard : d1866 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1607 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3953 pattern childGuard
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3956 pattern childGuard
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3958 (pattern : Twelve) (guard : d1866 pattern = 1) : d1281 pattern ≤ (0 : Int) + d1558 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1281, d1558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3903 pattern childGuard
    simpa only [d1281, d1558, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1281, d1558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3831 pattern childGuard
    simpa only [d1281, d1558, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3959 (pattern : Twelve) (guard : d1866 pattern = 1) : d1287 pattern ≤ (0 : Int) + d1567 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1287, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3946 pattern childGuard
    simpa only [d1287, d1567, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1287, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3958 pattern childGuard
    simpa only [d1287, d1567, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3960 (pattern : Twelve) (guard : d1866 pattern = 1) : d1297 pattern ≤ (0 : Int) + d1581 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1297, d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3710 pattern childGuard
    simpa only [d1297, d1581, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1297, d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3959 pattern childGuard
    simpa only [d1297, d1581, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3961 (pattern : Twelve) (guard : d1866 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1582 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1298, d1582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3854 pattern childGuard
    simpa only [d1298, d1582, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1298, d1582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1298, d1582, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3962 (pattern : Twelve) (guard : d1866 pattern = 1) : d1307 pattern ≤ (0 : Int) + d1594 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1307, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3960 pattern childGuard
    simpa only [d1307, d1594, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1307, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3961 pattern childGuard
    simpa only [d1307, d1594, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3963 (pattern : Twelve) (guard : d1866 pattern = 1) : d1277 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1277, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3587 pattern childGuard
    simpa only [d1277, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1277, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3828 pattern childGuard
    simpa only [d1277, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3964 (pattern : Twelve) (guard : d1866 pattern = 1) : d1282 pattern ≤ (0 : Int) + d1186 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1282, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3945 pattern childGuard
    simpa only [d1282, d1186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1282, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3963 pattern childGuard
    simpa only [d1282, d1186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3965 (pattern : Twelve) (guard : d1866 pattern = 1) : d1288 pattern ≤ (0 : Int) + d1568 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1288, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3964 pattern childGuard
    simpa only [d1288, d1568, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1288, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3832 pattern childGuard
    simpa only [d1288, d1568, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3966 (pattern : Twelve) (guard : d1866 pattern = 1) : d1299 pattern ≤ (0 : Int) + d1583 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1299, d1583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3883 pattern childGuard
    simpa only [d1299, d1583, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1299, d1583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3965 pattern childGuard
    simpa only [d1299, d1583, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3967 (pattern : Twelve) (guard : d1866 pattern = 1) : d1289 pattern ≤ (0 : Int) + d1569 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1289, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3884 pattern childGuard
    simpa only [d1289, d1569, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1289, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3761 pattern childGuard
    simpa only [d1289, d1569, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3968 (pattern : Twelve) (guard : d1866 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1584 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1300, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3967 pattern childGuard
    simpa only [d1300, d1584, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1300, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1300, d1584, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3969 (pattern : Twelve) (guard : d1866 pattern = 1) : d1308 pattern ≤ (0 : Int) + d1595 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1308, d1595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3966 pattern childGuard
    simpa only [d1308, d1595, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1308, d1595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3968 pattern childGuard
    simpa only [d1308, d1595, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3970 (pattern : Twelve) (guard : d1866 pattern = 1) : d1314 pattern ≤ (0 : Int) + d1602 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1314, d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3962 pattern childGuard
    simpa only [d1314, d1602, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1314, d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3969 pattern childGuard
    simpa only [d1314, d1602, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3971 (pattern : Twelve) (guard : d1866 pattern = 1) : d1315 pattern ≤ (0 : Int) + d1603 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1315, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3952 pattern childGuard
    simpa only [d1315, d1603, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1315, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1315, d1603, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3972 (pattern : Twelve) (guard : d1866 pattern = 1) : d1319 pattern ≤ (0 : Int) + d1608 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1319, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3970 pattern childGuard
    simpa only [d1319, d1608, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1319, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3971 pattern childGuard
    simpa only [d1319, d1608, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3973 (pattern : Twelve) (guard : d1866 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1610 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1321, d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3957 pattern childGuard
    simpa only [d1321, d1610, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1321, d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3972 pattern childGuard
    simpa only [d1321, d1610, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3974 (pattern : Twelve) (guard : d1866 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1611 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1321, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3956 pattern childGuard
    simpa only [d1321, d1611, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1321, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3972 pattern childGuard
    simpa only [d1321, d1611, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3975 (pattern : Twelve) (guard : d1866 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1613 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3973 pattern childGuard
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3974 pattern childGuard
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3976 (pattern : Twelve) (guard : d1866 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1614 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3975 pattern childGuard
    simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3974 pattern childGuard
    simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3977 (pattern : Twelve) (guard : d1866 pattern = 1) : d1324 pattern ≤ (0 : Int) + d635 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1324, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3602 pattern childGuard
    simpa only [d1324, d635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1324, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3372 pattern childGuard
    simpa only [d1324, d635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3978 (pattern : Twelve) (guard : d1866 pattern = 1) : d1325 pattern ≤ (0 : Int) + d1559 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1325, d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3939 pattern childGuard
    simpa only [d1325, d1559, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1325, d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3977 pattern childGuard
    simpa only [d1325, d1559, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3979 (pattern : Twelve) (guard : d1866 pattern = 1) : d1326 pattern ≤ (0 : Int) + d1560 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1326, d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3903 pattern childGuard
    simpa only [d1326, d1560, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1326, d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3977 pattern childGuard
    simpa only [d1326, d1560, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3980 (pattern : Twelve) (guard : d1866 pattern = 1) : d1333 pattern ≤ (0 : Int) + d1570 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1333, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3978 pattern childGuard
    simpa only [d1333, d1570, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1333, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3979 pattern childGuard
    simpa only [d1333, d1570, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3981 (pattern : Twelve) (guard : d1866 pattern = 1) : d1339 pattern ≤ (0 : Int) + d1585 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1339, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3701 pattern childGuard
    simpa only [d1339, d1585, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1339, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3980 pattern childGuard
    simpa only [d1339, d1585, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3982 (pattern : Twelve) (guard : d1866 pattern = 1) : d1345 pattern ≤ (0 : Int) + d1596 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1345, d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3981 pattern childGuard
    simpa only [d1345, d1596, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1345, d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3943 pattern childGuard
    simpa only [d1345, d1596, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3983 (pattern : Twelve) (guard : d1866 pattern = 1) : d1327 pattern ≤ (0 : Int) + d1185 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1327, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3939 pattern childGuard
    simpa only [d1327, d1185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1327, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3831 pattern childGuard
    simpa only [d1327, d1185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3984 (pattern : Twelve) (guard : d1866 pattern = 1) : d1334 pattern ≤ (0 : Int) + d1571 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1334, d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3983 pattern childGuard
    simpa only [d1334, d1571, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1334, d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3947 pattern childGuard
    simpa only [d1334, d1571, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3985 (pattern : Twelve) (guard : d1866 pattern = 1) : d1340 pattern ≤ (0 : Int) + d1586 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1340, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3862 pattern childGuard
    simpa only [d1340, d1586, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1340, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3984 pattern childGuard
    simpa only [d1340, d1586, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3986 (pattern : Twelve) (guard : d1866 pattern = 1) : d1346 pattern ≤ (0 : Int) + d1597 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1346, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3985 pattern childGuard
    simpa only [d1346, d1597, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1346, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3951 pattern childGuard
    simpa only [d1346, d1597, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3987 (pattern : Twelve) (guard : d1866 pattern = 1) : d1349 pattern ≤ (0 : Int) + d1604 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1349, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3982 pattern childGuard
    simpa only [d1349, d1604, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1349, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3986 pattern childGuard
    simpa only [d1349, d1604, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3988 (pattern : Twelve) (guard : d1866 pattern = 1) : d1328 pattern ≤ (0 : Int) + d1561 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1328, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3903 pattern childGuard
    simpa only [d1328, d1561, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1328, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3963 pattern childGuard
    simpa only [d1328, d1561, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3989 (pattern : Twelve) (guard : d1866 pattern = 1) : d1335 pattern ≤ (0 : Int) + d1572 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1335, d1572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3983 pattern childGuard
    simpa only [d1335, d1572, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1335, d1572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3988 pattern childGuard
    simpa only [d1335, d1572, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3990 (pattern : Twelve) (guard : d1866 pattern = 1) : d1341 pattern ≤ (0 : Int) + d1587 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1341, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3710 pattern childGuard
    simpa only [d1341, d1587, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1341, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3989 pattern childGuard
    simpa only [d1341, d1587, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3991 (pattern : Twelve) (guard : d1866 pattern = 1) : d1329 pattern ≤ (0 : Int) + d1562 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1329, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3687 pattern childGuard
    simpa only [d1329, d1562, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1329, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3697 pattern childGuard
    simpa only [d1329, d1562, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3992 (pattern : Twelve) (guard : d1866 pattern = 1) : d1336 pattern ≤ (0 : Int) + d1573 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1336, d1573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3854 pattern childGuard
    simpa only [d1336, d1573, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1336, d1573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3991 pattern childGuard
    simpa only [d1336, d1573, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3993 (pattern : Twelve) (guard : d1866 pattern = 1) : d1342 pattern ≤ (0 : Int) + d1588 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1342, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3992 pattern childGuard
    simpa only [d1342, d1588, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1342, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1342, d1588, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3994 (pattern : Twelve) (guard : d1866 pattern = 1) : d1347 pattern ≤ (0 : Int) + d1598 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1347, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3990 pattern childGuard
    simpa only [d1347, d1598, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1347, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3993 pattern childGuard
    simpa only [d1347, d1598, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3995 (pattern : Twelve) (guard : d1866 pattern = 1) : d1330 pattern ≤ (0 : Int) + d670 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1330, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3945 pattern childGuard
    simpa only [d1330, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1330, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1330, d670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3996 (pattern : Twelve) (guard : d1866 pattern = 1) : d1331 pattern ≤ (0 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1331, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3963 pattern childGuard
    simpa only [d1331, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1331, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1331, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3997 (pattern : Twelve) (guard : d1866 pattern = 1) : d1337 pattern ≤ (0 : Int) + d1574 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1337, d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3995 pattern childGuard
    simpa only [d1337, d1574, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1337, d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3996 pattern childGuard
    simpa only [d1337, d1574, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3998 (pattern : Twelve) (guard : d1866 pattern = 1) : d1343 pattern ≤ (0 : Int) + d1589 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1343, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3883 pattern childGuard
    simpa only [d1343, d1589, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1343, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3997 pattern childGuard
    simpa only [d1343, d1589, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3999 (pattern : Twelve) (guard : d1866 pattern = 1) : d1332 pattern ≤ (0 : Int) + d1563 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1332, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3760 pattern childGuard
    simpa only [d1332, d1563, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1332, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3706 pattern childGuard
    simpa only [d1332, d1563, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4000 (pattern : Twelve) (guard : d1866 pattern = 1) : d1338 pattern ≤ (0 : Int) + d1575 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1338, d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3999 pattern childGuard
    simpa only [d1338, d1575, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1338, d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3839 pattern childGuard
    simpa only [d1338, d1575, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4001 (pattern : Twelve) (guard : d1866 pattern = 1) : d1344 pattern ≤ (0 : Int) + d1590 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1344, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4000 pattern childGuard
    simpa only [d1344, d1590, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1344, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1344, d1590, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4002 (pattern : Twelve) (guard : d1866 pattern = 1) : d1348 pattern ≤ (0 : Int) + d1599 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1348, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3998 pattern childGuard
    simpa only [d1348, d1599, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1348, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4001 pattern childGuard
    simpa only [d1348, d1599, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4003 (pattern : Twelve) (guard : d1866 pattern = 1) : d1350 pattern ≤ (0 : Int) + d1605 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1350, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3994 pattern childGuard
    simpa only [d1350, d1605, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1350, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4002 pattern childGuard
    simpa only [d1350, d1605, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4004 (pattern : Twelve) (guard : d1866 pattern = 1) : d1351 pattern ≤ (0 : Int) + d1606 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1351, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3986 pattern childGuard
    simpa only [d1351, d1606, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1351, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1351, d1606, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4005 (pattern : Twelve) (guard : d1866 pattern = 1) : d1352 pattern ≤ (0 : Int) + d1609 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1352, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4003 pattern childGuard
    simpa only [d1352, d1609, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1352, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4004 pattern childGuard
    simpa only [d1352, d1609, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4006 (pattern : Twelve) (guard : d1866 pattern = 1) : d1353 pattern ≤ (0 : Int) + d1612 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1353, d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3987 pattern childGuard
    simpa only [d1353, d1612, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1353, d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4005 pattern childGuard
    simpa only [d1353, d1612, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4007 (pattern : Twelve) (guard : d1866 pattern = 1) : d1354 pattern ≤ (0 : Int) + d1615 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1354, d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3976 pattern childGuard
    simpa only [d1354, d1615, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1354, d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4006 pattern childGuard
    simpa only [d1354, d1615, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4008 (pattern : Twelve) (guard : d1866 pattern = 1) : d1649 pattern ≤ (0 : Int) + d1788 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1649, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3687 pattern childGuard
    simpa only [d1649, d1788, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1649, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3977 pattern childGuard
    simpa only [d1649, d1788, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4009 (pattern : Twelve) (guard : d1866 pattern = 1) : d1650 pattern ≤ (0 : Int) + d1789 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1650, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3760 pattern childGuard
    simpa only [d1650, d1789, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1650, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1650, d1789, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4010 (pattern : Twelve) (guard : d1866 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1797 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1656, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4008 pattern childGuard
    simpa only [d1656, d1797, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1656, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4009 pattern childGuard
    simpa only [d1656, d1797, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4011 (pattern : Twelve) (guard : d1866 pattern = 1) : d1644 pattern ≤ (0 : Int) + d1780 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1644, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3977 pattern childGuard
    simpa only [d1644, d1780, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1644, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3697 pattern childGuard
    simpa only [d1644, d1780, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4012 (pattern : Twelve) (guard : d1866 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1645, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3977 pattern childGuard
    simpa only [d1645, d1781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1645, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1645, d1781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4013 (pattern : Twelve) (guard : d1866 pattern = 1) : d1647 pattern ≤ (0 : Int) + d1784 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1647, d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4011 pattern childGuard
    simpa only [d1647, d1784, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1647, d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4012 pattern childGuard
    simpa only [d1647, d1784, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4014 (pattern : Twelve) (guard : d1866 pattern = 1) : d1651 pattern ≤ (0 : Int) + d1790 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1651, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3950 pattern childGuard
    simpa only [d1651, d1790, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1651, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4013 pattern childGuard
    simpa only [d1651, d1790, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4015 (pattern : Twelve) (guard : d1866 pattern = 1) : d1657 pattern ≤ (0 : Int) + d1798 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1657, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4014 pattern childGuard
    simpa only [d1657, d1798, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1657, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3968 pattern childGuard
    simpa only [d1657, d1798, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4016 (pattern : Twelve) (guard : d1866 pattern = 1) : d1660 pattern ≤ (0 : Int) + d1804 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1660, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4010 pattern childGuard
    simpa only [d1660, d1804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1660, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4015 pattern childGuard
    simpa only [d1660, d1804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4017 (pattern : Twelve) (guard : d1866 pattern = 1) : d1652 pattern ≤ (0 : Int) + d1791 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1652, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3854 pattern childGuard
    simpa only [d1652, d1791, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1652, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4011 pattern childGuard
    simpa only [d1652, d1791, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4018 (pattern : Twelve) (guard : d1866 pattern = 1) : d1653 pattern ≤ (0 : Int) + d1792 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1653, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3884 pattern childGuard
    simpa only [d1653, d1792, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1653, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1653, d1792, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4019 (pattern : Twelve) (guard : d1866 pattern = 1) : d1658 pattern ≤ (0 : Int) + d1799 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1658, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4017 pattern childGuard
    simpa only [d1658, d1799, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1658, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4018 pattern childGuard
    simpa only [d1658, d1799, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4020 (pattern : Twelve) (guard : d1866 pattern = 1) : d1646 pattern ≤ (0 : Int) + d1782 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1646, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3697 pattern childGuard
    simpa only [d1646, d1782, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1646, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3706 pattern childGuard
    simpa only [d1646, d1782, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4021 (pattern : Twelve) (guard : d1866 pattern = 1) : d1648 pattern ≤ (0 : Int) + d1785 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1648, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4020 pattern childGuard
    simpa only [d1648, d1785, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1648, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3839 pattern childGuard
    simpa only [d1648, d1785, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4022 (pattern : Twelve) (guard : d1866 pattern = 1) : d1654 pattern ≤ (0 : Int) + d1793 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1654, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3967 pattern childGuard
    simpa only [d1654, d1793, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1654, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4021 pattern childGuard
    simpa only [d1654, d1793, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4023 (pattern : Twelve) (guard : d1866 pattern = 1) : d1655 pattern ≤ (0 : Int) + d1655 pattern := by
  omega
theorem c4024 (pattern : Twelve) (guard : d1866 pattern = 1) : d1659 pattern ≤ (0 : Int) + d1800 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1659, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4022 pattern childGuard
    simpa only [d1659, d1800, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1659, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4023 pattern childGuard
    simpa only [d1659, d1800, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4025 (pattern : Twelve) (guard : d1866 pattern = 1) : d1661 pattern ≤ (0 : Int) + d1805 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1661, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4019 pattern childGuard
    simpa only [d1661, d1805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1661, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4024 pattern childGuard
    simpa only [d1661, d1805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4026 (pattern : Twelve) (guard : d1866 pattern = 1) : d1662 pattern ≤ (0 : Int) + d1806 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1662, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4015 pattern childGuard
    simpa only [d1662, d1806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1662, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1662, d1806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4027 (pattern : Twelve) (guard : d1866 pattern = 1) : d1663 pattern ≤ (0 : Int) + d1809 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1663, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4025 pattern childGuard
    simpa only [d1663, d1809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1663, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4026 pattern childGuard
    simpa only [d1663, d1809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4028 (pattern : Twelve) (guard : d1866 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1811 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1664, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4016 pattern childGuard
    simpa only [d1664, d1811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1664, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4027 pattern childGuard
    simpa only [d1664, d1811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4029 (pattern : Twelve) (guard : d1866 pattern = 1) : d1668 pattern ≤ (0 : Int) + d1794 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1668, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3687 pattern childGuard
    simpa only [d1668, d1794, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1668, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4011 pattern childGuard
    simpa only [d1668, d1794, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4030 (pattern : Twelve) (guard : d1866 pattern = 1) : d1671 pattern ≤ (0 : Int) + d1801 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1671, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4029 pattern childGuard
    simpa only [d1671, d1801, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1671, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4009 pattern childGuard
    simpa only [d1671, d1801, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4031 (pattern : Twelve) (guard : d1866 pattern = 1) : d1674 pattern ≤ (0 : Int) + d1807 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1674, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4030 pattern childGuard
    simpa only [d1674, d1807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1674, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4015 pattern childGuard
    simpa only [d1674, d1807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4032 (pattern : Twelve) (guard : d1866 pattern = 1) : d1665 pattern ≤ (0 : Int) + d1783 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1665, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3977 pattern childGuard
    simpa only [d1665, d1783, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1665, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3706 pattern childGuard
    simpa only [d1665, d1783, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4033 (pattern : Twelve) (guard : d1866 pattern = 1) : d1666 pattern ≤ (0 : Int) + d1786 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1666, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4011 pattern childGuard
    simpa only [d1666, d1786, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1666, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4032 pattern childGuard
    simpa only [d1666, d1786, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4034 (pattern : Twelve) (guard : d1866 pattern = 1) : d1669 pattern ≤ (0 : Int) + d1795 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1669, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3854 pattern childGuard
    simpa only [d1669, d1795, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1669, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4033 pattern childGuard
    simpa only [d1669, d1795, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4035 (pattern : Twelve) (guard : d1866 pattern = 1) : d1672 pattern ≤ (0 : Int) + d1802 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1672, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4034 pattern childGuard
    simpa only [d1672, d1802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1672, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3968 pattern childGuard
    simpa only [d1672, d1802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4036 (pattern : Twelve) (guard : d1866 pattern = 1) : d183 pattern ≤ (0 : Int) + d183 pattern := by
  omega
theorem c4037 (pattern : Twelve) (guard : d1866 pattern = 1) : d1667 pattern ≤ (0 : Int) + d1787 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1667, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3839 pattern childGuard
    simpa only [d1667, d1787, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1667, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4036 pattern childGuard
    simpa only [d1667, d1787, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4038 (pattern : Twelve) (guard : d1866 pattern = 1) : d1670 pattern ≤ (0 : Int) + d1796 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1670, d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3967 pattern childGuard
    simpa only [d1670, d1796, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1670, d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4037 pattern childGuard
    simpa only [d1670, d1796, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4039 (pattern : Twelve) (guard : d1866 pattern = 1) : d1626 pattern ≤ (0 : Int) + d1626 pattern := by
  omega
theorem c4040 (pattern : Twelve) (guard : d1866 pattern = 1) : d1673 pattern ≤ (0 : Int) + d1803 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1673, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4038 pattern childGuard
    simpa only [d1673, d1803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1673, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4039 pattern childGuard
    simpa only [d1673, d1803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4041 (pattern : Twelve) (guard : d1866 pattern = 1) : d1675 pattern ≤ (0 : Int) + d1808 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1675, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4035 pattern childGuard
    simpa only [d1675, d1808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1675, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4040 pattern childGuard
    simpa only [d1675, d1808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4042 (pattern : Twelve) (guard : d1866 pattern = 1) : d1676 pattern ≤ (0 : Int) + d1810 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1676, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4041 pattern childGuard
    simpa only [d1676, d1810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1676, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4026 pattern childGuard
    simpa only [d1676, d1810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4043 (pattern : Twelve) (guard : d1866 pattern = 1) : d1677 pattern ≤ (0 : Int) + d1812 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1677, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4031 pattern childGuard
    simpa only [d1677, d1812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1677, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4042 pattern childGuard
    simpa only [d1677, d1812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4044 (pattern : Twelve) (guard : d1866 pattern = 1) : d1678 pattern ≤ (0 : Int) + d1813 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1678, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4028 pattern childGuard
    simpa only [d1678, d1813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1678, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4043 pattern childGuard
    simpa only [d1678, d1813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4045 (pattern : Twelve) (guard : d0 pattern = 1) : d217 pattern ≤ (0 : Int) + d223 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4046 (pattern : Twelve) (guard : d1842 pattern = 1) : d345 pattern ≤ (0 : Int) + d228 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d345, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6 pattern childGuard
    simpa only [d1842, d345, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d345, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4045 pattern childGuard
    simpa only [d1842, d345, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4047 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d225 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4048 (pattern : Twelve) (guard : d1842 pattern = 1) : d346 pattern ≤ (0 : Int) + d229 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d346, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13 pattern childGuard
    simpa only [d1842, d346, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d346, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4047 pattern childGuard
    simpa only [d1842, d346, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4049 (pattern : Twelve) (guard : d1842 pattern = 1) : d348 pattern ≤ (0 : Int) + d231 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d348, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4046 pattern childGuard
    simpa only [d348, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d348, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4048 pattern childGuard
    simpa only [d348, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4050 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d227 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4051 (pattern : Twelve) (guard : d1842 pattern = 1) : d347 pattern ≤ (0 : Int) + d230 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d347, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20 pattern childGuard
    simpa only [d1842, d347, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d347, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4050 pattern childGuard
    simpa only [d1842, d347, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4052 (pattern : Twelve) (guard : d1842 pattern = 1) : d349 pattern ≤ (0 : Int) + d232 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d349, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4051 pattern childGuard
    simpa only [d349, d232, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d349, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4048 pattern childGuard
    simpa only [d349, d232, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4053 (pattern : Twelve) (guard : d1842 pattern = 1) : d350 pattern ≤ (0 : Int) + d233 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d350, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4049 pattern childGuard
    simpa only [d350, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d350, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4052 pattern childGuard
    simpa only [d350, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4054 (pattern : Twelve) (guard : d1842 pattern = 1) : d351 pattern ≤ (0 : Int) + d234 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d351, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4053 pattern childGuard
    simpa only [d351, d234, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d351, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4052 pattern childGuard
    simpa only [d351, d234, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4055 (pattern : Twelve) (guard : d0 pattern = 1) : d922 pattern ≤ (0 : Int) + d928 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4056 (pattern : Twelve) (guard : d1842 pattern = 1) : d1011 pattern ≤ (0 : Int) + d933 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d1011, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c29 pattern childGuard
    simpa only [d1842, d1011, d933, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d1011, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4055 pattern childGuard
    simpa only [d1842, d1011, d933, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4057 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d930 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4058 (pattern : Twelve) (guard : d1842 pattern = 1) : d1012 pattern ≤ (0 : Int) + d934 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d1012, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c36 pattern childGuard
    simpa only [d1842, d1012, d934, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d1012, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4057 pattern childGuard
    simpa only [d1842, d1012, d934, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4059 (pattern : Twelve) (guard : d1842 pattern = 1) : d1014 pattern ≤ (0 : Int) + d936 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1014, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4056 pattern childGuard
    simpa only [d1014, d936, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1014, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4058 pattern childGuard
    simpa only [d1014, d936, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
