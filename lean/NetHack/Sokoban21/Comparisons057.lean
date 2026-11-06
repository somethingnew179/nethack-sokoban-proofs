/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons056
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c7980 (pattern : Twelve) (guard : d1866 pattern = 1) : d1242 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1242, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7975 pattern childGuard
    simpa only [d1242, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1242, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7979 pattern childGuard
    simpa only [d1242, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7981 (pattern : Twelve) (guard : d1866 pattern = 1) : d1244 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7972 pattern childGuard
    simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7980 pattern childGuard
    simpa only [d1244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7982 (pattern : Twelve) (guard : d1866 pattern = 1) : d1245 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7981 pattern childGuard
    simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7980 pattern childGuard
    simpa only [d1245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7983 (pattern : Twelve) (guard : d1866 pattern = 1) : d157 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7736 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7747 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7984 (pattern : Twelve) (guard : d1866 pattern = 1) : d661 pattern ≤ (0 : Int) + d874 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d661, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d661, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d661, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7983 pattern childGuard
    simpa only [d661, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7985 (pattern : Twelve) (guard : d1866 pattern = 1) : d1183 pattern ≤ (0 : Int) + d875 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1183, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7929 pattern childGuard
    simpa only [d1183, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1183, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7983 pattern childGuard
    simpa only [d1183, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7986 (pattern : Twelve) (guard : d1866 pattern = 1) : d1193 pattern ≤ (0 : Int) + d882 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1193, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7984 pattern childGuard
    simpa only [d1193, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1193, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7985 pattern childGuard
    simpa only [d1193, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7987 (pattern : Twelve) (guard : d1866 pattern = 1) : d1208 pattern ≤ (0 : Int) + d890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1208, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7732 pattern childGuard
    simpa only [d1208, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1208, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7986 pattern childGuard
    simpa only [d1208, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7988 (pattern : Twelve) (guard : d1866 pattern = 1) : d1187 pattern ≤ (0 : Int) + d876 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1187, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7753 pattern childGuard
    simpa only [d1187, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1187, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3702 pattern childGuard
    simpa only [d1187, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7989 (pattern : Twelve) (guard : d1866 pattern = 1) : d1196 pattern ≤ (0 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1196, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7988 pattern childGuard
    simpa only [d1196, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1196, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7839 pattern childGuard
    simpa only [d1196, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7990 (pattern : Twelve) (guard : d1866 pattern = 1) : d1210 pattern ≤ (0 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1210, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d1210, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1210, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7989 pattern childGuard
    simpa only [d1210, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7991 (pattern : Twelve) (guard : d1866 pattern = 1) : d1224 pattern ≤ (0 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1224, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7987 pattern childGuard
    simpa only [d1224, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1224, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7990 pattern childGuard
    simpa only [d1224, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7992 (pattern : Twelve) (guard : d1866 pattern = 1) : d674 pattern ≤ (0 : Int) + d877 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d674, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d674, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d674, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7960 pattern childGuard
    simpa only [d674, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7993 (pattern : Twelve) (guard : d1866 pattern = 1) : d705 pattern ≤ (0 : Int) + d884 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d705, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7992 pattern childGuard
    simpa only [d705, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d705, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7940 pattern childGuard
    simpa only [d705, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7994 (pattern : Twelve) (guard : d1866 pattern = 1) : d731 pattern ≤ (0 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d731, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7804 pattern childGuard
    simpa only [d731, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d731, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7993 pattern childGuard
    simpa only [d731, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7995 (pattern : Twelve) (guard : d1866 pattern = 1) : d1211 pattern ≤ (0 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1211, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7943 pattern childGuard
    simpa only [d1211, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1211, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7989 pattern childGuard
    simpa only [d1211, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7996 (pattern : Twelve) (guard : d1866 pattern = 1) : d1225 pattern ≤ (0 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1225, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7994 pattern childGuard
    simpa only [d1225, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1225, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7995 pattern childGuard
    simpa only [d1225, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7997 (pattern : Twelve) (guard : d1866 pattern = 1) : d1234 pattern ≤ (0 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1234, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7991 pattern childGuard
    simpa only [d1234, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1234, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7996 pattern childGuard
    simpa only [d1234, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7998 (pattern : Twelve) (guard : d1866 pattern = 1) : d1188 pattern ≤ (0 : Int) + d878 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1188, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7929 pattern childGuard
    simpa only [d1188, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1188, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7835 pattern childGuard
    simpa only [d1188, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7999 (pattern : Twelve) (guard : d1866 pattern = 1) : d1197 pattern ≤ (0 : Int) + d885 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1197, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7992 pattern childGuard
    simpa only [d1197, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1197, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7998 pattern childGuard
    simpa only [d1197, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8000 (pattern : Twelve) (guard : d1866 pattern = 1) : d1212 pattern ≤ (0 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1212, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7800 pattern childGuard
    simpa only [d1212, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1212, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7999 pattern childGuard
    simpa only [d1212, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8001 (pattern : Twelve) (guard : d1866 pattern = 1) : d666 pattern ≤ (0 : Int) + d879 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d666, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d666, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d666, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7912 pattern childGuard
    simpa only [d666, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8002 (pattern : Twelve) (guard : d1866 pattern = 1) : d704 pattern ≤ (0 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d704, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7777 pattern childGuard
    simpa only [d704, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d704, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8001 pattern childGuard
    simpa only [d704, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8003 (pattern : Twelve) (guard : d1866 pattern = 1) : d1213 pattern ≤ (0 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1213, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8002 pattern childGuard
    simpa only [d1213, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1213, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7989 pattern childGuard
    simpa only [d1213, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8004 (pattern : Twelve) (guard : d1866 pattern = 1) : d1226 pattern ≤ (0 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1226, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8000 pattern childGuard
    simpa only [d1226, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1226, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8003 pattern childGuard
    simpa only [d1226, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8005 (pattern : Twelve) (guard : d1866 pattern = 1) : d639 pattern ≤ (0 : Int) + d873 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d639, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7911 pattern childGuard
    simpa only [d639, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d639, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7834 pattern childGuard
    simpa only [d639, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8006 (pattern : Twelve) (guard : d1866 pattern = 1) : d679 pattern ≤ (0 : Int) + d880 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d679, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8005 pattern childGuard
    simpa only [d679, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d679, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d679, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8007 (pattern : Twelve) (guard : d1866 pattern = 1) : d708 pattern ≤ (0 : Int) + d887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d708, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7919 pattern childGuard
    simpa only [d708, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d708, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8006 pattern childGuard
    simpa only [d708, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8008 (pattern : Twelve) (guard : d1866 pattern = 1) : d1214 pattern ≤ (0 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1214, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7833 pattern childGuard
    simpa only [d1214, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1214, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8007 pattern childGuard
    simpa only [d1214, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8009 (pattern : Twelve) (guard : d1866 pattern = 1) : d676 pattern ≤ (0 : Int) + d881 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d676, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7776 pattern childGuard
    simpa only [d676, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d676, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7909 pattern childGuard
    simpa only [d676, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8010 (pattern : Twelve) (guard : d1866 pattern = 1) : d707 pattern ≤ (0 : Int) + d888 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d707, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8009 pattern childGuard
    simpa only [d707, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d707, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7913 pattern childGuard
    simpa only [d707, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8011 (pattern : Twelve) (guard : d1866 pattern = 1) : d1198 pattern ≤ (0 : Int) + d889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1198, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7839 pattern childGuard
    simpa only [d1198, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1198, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1198, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8012 (pattern : Twelve) (guard : d1866 pattern = 1) : d1215 pattern ≤ (0 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1215, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8010 pattern childGuard
    simpa only [d1215, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1215, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8011 pattern childGuard
    simpa only [d1215, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8013 (pattern : Twelve) (guard : d1866 pattern = 1) : d1227 pattern ≤ (0 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1227, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8008 pattern childGuard
    simpa only [d1227, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1227, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8012 pattern childGuard
    simpa only [d1227, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8014 (pattern : Twelve) (guard : d1866 pattern = 1) : d1235 pattern ≤ (0 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1235, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8004 pattern childGuard
    simpa only [d1235, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1235, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8013 pattern childGuard
    simpa only [d1235, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8015 (pattern : Twelve) (guard : d1866 pattern = 1) : d1236 pattern ≤ (0 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1236, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7996 pattern childGuard
    simpa only [d1236, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1236, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1236, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8016 (pattern : Twelve) (guard : d1866 pattern = 1) : d1240 pattern ≤ (0 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1240, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8014 pattern childGuard
    simpa only [d1240, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1240, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8015 pattern childGuard
    simpa only [d1240, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8017 (pattern : Twelve) (guard : d1866 pattern = 1) : d1243 pattern ≤ (0 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1243, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7997 pattern childGuard
    simpa only [d1243, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1243, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8016 pattern childGuard
    simpa only [d1243, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8018 (pattern : Twelve) (guard : d1866 pattern = 1) : d1246 pattern ≤ (0 : Int) + d907 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1246, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7982 pattern childGuard
    simpa only [d1246, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1246, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8017 pattern childGuard
    simpa only [d1246, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8019 (pattern : Twelve) (guard : d1866 pattern = 1) : d636 pattern ≤ (0 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d636, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7739 pattern childGuard
    simpa only [d636, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d636, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7747 pattern childGuard
    simpa only [d636, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8020 (pattern : Twelve) (guard : d1866 pattern = 1) : d1183 pattern ≤ (0 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1183, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8019 pattern childGuard
    simpa only [d1183, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1183, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7983 pattern childGuard
    simpa only [d1183, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8021 (pattern : Twelve) (guard : d1866 pattern = 1) : d1564 pattern ≤ (0 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1564, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8020 pattern childGuard
    simpa only [d1564, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1564, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7983 pattern childGuard
    simpa only [d1564, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8022 (pattern : Twelve) (guard : d1866 pattern = 1) : d1576 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1576, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7934 pattern childGuard
    simpa only [d1576, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1576, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8021 pattern childGuard
    simpa only [d1576, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8023 (pattern : Twelve) (guard : d1866 pattern = 1) : d1577 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1577, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7753 pattern childGuard
    simpa only [d1577, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1577, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1577, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8024 (pattern : Twelve) (guard : d1866 pattern = 1) : d1591 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1591, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8022 pattern childGuard
    simpa only [d1591, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1591, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8023 pattern childGuard
    simpa only [d1591, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8025 (pattern : Twelve) (guard : d1866 pattern = 1) : d644 pattern ≤ (0 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d644, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7748 pattern childGuard
    simpa only [d644, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d644, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7911 pattern childGuard
    simpa only [d644, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8026 (pattern : Twelve) (guard : d1866 pattern = 1) : d1184 pattern ≤ (0 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1184, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8019 pattern childGuard
    simpa only [d1184, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1184, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8025 pattern childGuard
    simpa only [d1184, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8027 (pattern : Twelve) (guard : d1866 pattern = 1) : d1557 pattern ≤ (0 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1557, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7983 pattern childGuard
    simpa only [d1557, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1557, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1557, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8028 (pattern : Twelve) (guard : d1866 pattern = 1) : d1565 pattern ≤ (0 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1565, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8026 pattern childGuard
    simpa only [d1565, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1565, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8027 pattern childGuard
    simpa only [d1565, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8029 (pattern : Twelve) (guard : d1866 pattern = 1) : d1578 pattern ≤ (0 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1578, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7943 pattern childGuard
    simpa only [d1578, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1578, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8028 pattern childGuard
    simpa only [d1578, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8030 (pattern : Twelve) (guard : d1866 pattern = 1) : d1566 pattern ≤ (0 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1566, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7935 pattern childGuard
    simpa only [d1566, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1566, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7754 pattern childGuard
    simpa only [d1566, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8031 (pattern : Twelve) (guard : d1866 pattern = 1) : d1579 pattern ≤ (0 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1579, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8030 pattern childGuard
    simpa only [d1579, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1579, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1579, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8032 (pattern : Twelve) (guard : d1866 pattern = 1) : d1592 pattern ≤ (0 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1592, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8029 pattern childGuard
    simpa only [d1592, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1592, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8031 pattern childGuard
    simpa only [d1592, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8033 (pattern : Twelve) (guard : d1866 pattern = 1) : d1600 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1600, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8024 pattern childGuard
    simpa only [d1600, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1600, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8032 pattern childGuard
    simpa only [d1600, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8034 (pattern : Twelve) (guard : d1866 pattern = 1) : d1580 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1580, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d1580, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1580, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8021 pattern childGuard
    simpa only [d1580, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8035 (pattern : Twelve) (guard : d1866 pattern = 1) : d1593 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1593, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8034 pattern childGuard
    simpa only [d1593, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1593, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8023 pattern childGuard
    simpa only [d1593, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8036 (pattern : Twelve) (guard : d1866 pattern = 1) : d1601 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1601, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8035 pattern childGuard
    simpa only [d1601, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1601, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8032 pattern childGuard
    simpa only [d1601, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8037 (pattern : Twelve) (guard : d1866 pattern = 1) : d1607 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8033 pattern childGuard
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8036 pattern childGuard
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8038 (pattern : Twelve) (guard : d1866 pattern = 1) : d1558 pattern ≤ (0 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1558, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7983 pattern childGuard
    simpa only [d1558, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1558, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7912 pattern childGuard
    simpa only [d1558, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8039 (pattern : Twelve) (guard : d1866 pattern = 1) : d1567 pattern ≤ (0 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1567, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8026 pattern childGuard
    simpa only [d1567, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1567, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8038 pattern childGuard
    simpa only [d1567, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8040 (pattern : Twelve) (guard : d1866 pattern = 1) : d1581 pattern ≤ (0 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1581, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7777 pattern childGuard
    simpa only [d1581, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1581, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8039 pattern childGuard
    simpa only [d1581, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8041 (pattern : Twelve) (guard : d1866 pattern = 1) : d1582 pattern ≤ (0 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1582, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7935 pattern childGuard
    simpa only [d1582, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1582, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1582, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8042 (pattern : Twelve) (guard : d1866 pattern = 1) : d1594 pattern ≤ (0 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1594, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8040 pattern childGuard
    simpa only [d1594, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1594, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8041 pattern childGuard
    simpa only [d1594, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8043 (pattern : Twelve) (guard : d1866 pattern = 1) : d21 pattern ≤ (0 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d21, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7834 pattern childGuard
    simpa only [d21, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d21, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3828 pattern childGuard
    simpa only [d21, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8044 (pattern : Twelve) (guard : d1866 pattern = 1) : d1186 pattern ≤ (0 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1186, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8025 pattern childGuard
    simpa only [d1186, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1186, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8043 pattern childGuard
    simpa only [d1186, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8045 (pattern : Twelve) (guard : d1866 pattern = 1) : d1568 pattern ≤ (0 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1568, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8044 pattern childGuard
    simpa only [d1568, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1568, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7913 pattern childGuard
    simpa only [d1568, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8046 (pattern : Twelve) (guard : d1866 pattern = 1) : d1583 pattern ≤ (0 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1583, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7964 pattern childGuard
    simpa only [d1583, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1583, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8045 pattern childGuard
    simpa only [d1583, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8047 (pattern : Twelve) (guard : d1866 pattern = 1) : d1569 pattern ≤ (0 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1569, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7965 pattern childGuard
    simpa only [d1569, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1569, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7839 pattern childGuard
    simpa only [d1569, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8048 (pattern : Twelve) (guard : d1866 pattern = 1) : d1584 pattern ≤ (0 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1584, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8047 pattern childGuard
    simpa only [d1584, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1584, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1584, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8049 (pattern : Twelve) (guard : d1866 pattern = 1) : d1595 pattern ≤ (0 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1595, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8046 pattern childGuard
    simpa only [d1595, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1595, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8048 pattern childGuard
    simpa only [d1595, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8050 (pattern : Twelve) (guard : d1866 pattern = 1) : d1602 pattern ≤ (0 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1602, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8042 pattern childGuard
    simpa only [d1602, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1602, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8049 pattern childGuard
    simpa only [d1602, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8051 (pattern : Twelve) (guard : d1866 pattern = 1) : d1603 pattern ≤ (0 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1603, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8032 pattern childGuard
    simpa only [d1603, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1603, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1603, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8052 (pattern : Twelve) (guard : d1866 pattern = 1) : d1608 pattern ≤ (0 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1608, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8050 pattern childGuard
    simpa only [d1608, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1608, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8051 pattern childGuard
    simpa only [d1608, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8053 (pattern : Twelve) (guard : d1866 pattern = 1) : d1610 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1610, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8037 pattern childGuard
    simpa only [d1610, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1610, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8052 pattern childGuard
    simpa only [d1610, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8054 (pattern : Twelve) (guard : d1866 pattern = 1) : d1611 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1611, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8036 pattern childGuard
    simpa only [d1611, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1611, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8052 pattern childGuard
    simpa only [d1611, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8055 (pattern : Twelve) (guard : d1866 pattern = 1) : d1613 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8053 pattern childGuard
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8054 pattern childGuard
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8056 (pattern : Twelve) (guard : d1866 pattern = 1) : d1614 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8055 pattern childGuard
    simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8054 pattern childGuard
    simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8057 (pattern : Twelve) (guard : d1866 pattern = 1) : d635 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d635, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7752 pattern childGuard
    simpa only [d635, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d635, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7837 pattern childGuard
    simpa only [d635, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8058 (pattern : Twelve) (guard : d1866 pattern = 1) : d1559 pattern ≤ (0 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1559, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8019 pattern childGuard
    simpa only [d1559, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1559, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8057 pattern childGuard
    simpa only [d1559, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8059 (pattern : Twelve) (guard : d1866 pattern = 1) : d1560 pattern ≤ (0 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1560, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7983 pattern childGuard
    simpa only [d1560, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1560, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8057 pattern childGuard
    simpa only [d1560, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8060 (pattern : Twelve) (guard : d1866 pattern = 1) : d1570 pattern ≤ (0 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1570, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8058 pattern childGuard
    simpa only [d1570, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1570, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8059 pattern childGuard
    simpa only [d1570, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8061 (pattern : Twelve) (guard : d1866 pattern = 1) : d1585 pattern ≤ (0 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1585, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7770 pattern childGuard
    simpa only [d1585, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1585, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8060 pattern childGuard
    simpa only [d1585, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8062 (pattern : Twelve) (guard : d1866 pattern = 1) : d1596 pattern ≤ (0 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1596, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8061 pattern childGuard
    simpa only [d1596, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1596, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8023 pattern childGuard
    simpa only [d1596, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8063 (pattern : Twelve) (guard : d1866 pattern = 1) : d1185 pattern ≤ (0 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1185, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8019 pattern childGuard
    simpa only [d1185, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1185, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7912 pattern childGuard
    simpa only [d1185, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8064 (pattern : Twelve) (guard : d1866 pattern = 1) : d1571 pattern ≤ (0 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1571, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8063 pattern childGuard
    simpa only [d1571, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1571, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8027 pattern childGuard
    simpa only [d1571, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8065 (pattern : Twelve) (guard : d1866 pattern = 1) : d1586 pattern ≤ (0 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1586, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7943 pattern childGuard
    simpa only [d1586, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1586, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8064 pattern childGuard
    simpa only [d1586, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8066 (pattern : Twelve) (guard : d1866 pattern = 1) : d1597 pattern ≤ (0 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1597, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8065 pattern childGuard
    simpa only [d1597, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1597, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8031 pattern childGuard
    simpa only [d1597, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8067 (pattern : Twelve) (guard : d1866 pattern = 1) : d1604 pattern ≤ (0 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1604, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8062 pattern childGuard
    simpa only [d1604, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1604, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8066 pattern childGuard
    simpa only [d1604, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8068 (pattern : Twelve) (guard : d1866 pattern = 1) : d1561 pattern ≤ (0 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1561, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7983 pattern childGuard
    simpa only [d1561, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1561, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8043 pattern childGuard
    simpa only [d1561, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8069 (pattern : Twelve) (guard : d1866 pattern = 1) : d1572 pattern ≤ (0 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1572, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8063 pattern childGuard
    simpa only [d1572, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1572, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8068 pattern childGuard
    simpa only [d1572, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8070 (pattern : Twelve) (guard : d1866 pattern = 1) : d1587 pattern ≤ (0 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1587, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7777 pattern childGuard
    simpa only [d1587, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1587, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8069 pattern childGuard
    simpa only [d1587, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8071 (pattern : Twelve) (guard : d1866 pattern = 1) : d1562 pattern ≤ (0 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1562, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7753 pattern childGuard
    simpa only [d1562, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1562, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7766 pattern childGuard
    simpa only [d1562, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8072 (pattern : Twelve) (guard : d1866 pattern = 1) : d1573 pattern ≤ (0 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1573, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7935 pattern childGuard
    simpa only [d1573, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1573, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8071 pattern childGuard
    simpa only [d1573, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8073 (pattern : Twelve) (guard : d1866 pattern = 1) : d1588 pattern ≤ (0 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1588, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8072 pattern childGuard
    simpa only [d1588, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1588, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1588, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8074 (pattern : Twelve) (guard : d1866 pattern = 1) : d1598 pattern ≤ (0 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1598, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8070 pattern childGuard
    simpa only [d1598, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1598, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8073 pattern childGuard
    simpa only [d1598, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8075 (pattern : Twelve) (guard : d1866 pattern = 1) : d670 pattern ≤ (0 : Int) + d1330 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d670, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8025 pattern childGuard
    simpa only [d670, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d670, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d670, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8076 (pattern : Twelve) (guard : d1866 pattern = 1) : d822 pattern ≤ (0 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d822, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8043 pattern childGuard
    simpa only [d822, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d822, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d822, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8077 (pattern : Twelve) (guard : d1866 pattern = 1) : d1574 pattern ≤ (0 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1574, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8075 pattern childGuard
    simpa only [d1574, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1574, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8076 pattern childGuard
    simpa only [d1574, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8078 (pattern : Twelve) (guard : d1866 pattern = 1) : d1589 pattern ≤ (0 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1589, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7964 pattern childGuard
    simpa only [d1589, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1589, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8077 pattern childGuard
    simpa only [d1589, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8079 (pattern : Twelve) (guard : d1866 pattern = 1) : d1563 pattern ≤ (0 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1563, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7838 pattern childGuard
    simpa only [d1563, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1563, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3706 pattern childGuard
    simpa only [d1563, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8080 (pattern : Twelve) (guard : d1866 pattern = 1) : d1575 pattern ≤ (0 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1575, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8079 pattern childGuard
    simpa only [d1575, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1575, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7920 pattern childGuard
    simpa only [d1575, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8081 (pattern : Twelve) (guard : d1866 pattern = 1) : d1590 pattern ≤ (0 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1590, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8080 pattern childGuard
    simpa only [d1590, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1590, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1590, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8082 (pattern : Twelve) (guard : d1866 pattern = 1) : d1599 pattern ≤ (0 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1599, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8078 pattern childGuard
    simpa only [d1599, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1599, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8081 pattern childGuard
    simpa only [d1599, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8083 (pattern : Twelve) (guard : d1866 pattern = 1) : d1605 pattern ≤ (0 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1605, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8074 pattern childGuard
    simpa only [d1605, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1605, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8082 pattern childGuard
    simpa only [d1605, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8084 (pattern : Twelve) (guard : d1866 pattern = 1) : d1606 pattern ≤ (0 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1606, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8066 pattern childGuard
    simpa only [d1606, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1606, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1606, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8085 (pattern : Twelve) (guard : d1866 pattern = 1) : d1609 pattern ≤ (0 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1609, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8083 pattern childGuard
    simpa only [d1609, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1609, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8084 pattern childGuard
    simpa only [d1609, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8086 (pattern : Twelve) (guard : d1866 pattern = 1) : d1612 pattern ≤ (0 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1612, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8067 pattern childGuard
    simpa only [d1612, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1612, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8085 pattern childGuard
    simpa only [d1612, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8087 (pattern : Twelve) (guard : d1866 pattern = 1) : d1615 pattern ≤ (0 : Int) + d1354 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1615, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8056 pattern childGuard
    simpa only [d1615, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1615, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8086 pattern childGuard
    simpa only [d1615, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8088 (pattern : Twelve) (guard : d1866 pattern = 1) : d1788 pattern ≤ (0 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1788, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7753 pattern childGuard
    simpa only [d1788, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1788, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8057 pattern childGuard
    simpa only [d1788, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8089 (pattern : Twelve) (guard : d1866 pattern = 1) : d1789 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1789, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7838 pattern childGuard
    simpa only [d1789, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1789, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1789, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8090 (pattern : Twelve) (guard : d1866 pattern = 1) : d1797 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1797, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8088 pattern childGuard
    simpa only [d1797, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1797, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8089 pattern childGuard
    simpa only [d1797, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8091 (pattern : Twelve) (guard : d1866 pattern = 1) : d1780 pattern ≤ (0 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1780, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8057 pattern childGuard
    simpa only [d1780, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1780, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7766 pattern childGuard
    simpa only [d1780, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8092 (pattern : Twelve) (guard : d1866 pattern = 1) : d1781 pattern ≤ (0 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1781, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8057 pattern childGuard
    simpa only [d1781, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1781, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1781, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8093 (pattern : Twelve) (guard : d1866 pattern = 1) : d1784 pattern ≤ (0 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1784, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8091 pattern childGuard
    simpa only [d1784, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1784, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8092 pattern childGuard
    simpa only [d1784, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8094 (pattern : Twelve) (guard : d1866 pattern = 1) : d1790 pattern ≤ (0 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1790, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8030 pattern childGuard
    simpa only [d1790, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1790, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8093 pattern childGuard
    simpa only [d1790, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8095 (pattern : Twelve) (guard : d1866 pattern = 1) : d1798 pattern ≤ (0 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1798, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8094 pattern childGuard
    simpa only [d1798, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1798, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8048 pattern childGuard
    simpa only [d1798, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8096 (pattern : Twelve) (guard : d1866 pattern = 1) : d1804 pattern ≤ (0 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1804, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8090 pattern childGuard
    simpa only [d1804, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1804, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8095 pattern childGuard
    simpa only [d1804, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8097 (pattern : Twelve) (guard : d1866 pattern = 1) : d1791 pattern ≤ (0 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1791, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7935 pattern childGuard
    simpa only [d1791, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1791, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8091 pattern childGuard
    simpa only [d1791, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8098 (pattern : Twelve) (guard : d1866 pattern = 1) : d1792 pattern ≤ (0 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1792, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7965 pattern childGuard
    simpa only [d1792, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1792, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1792, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8099 (pattern : Twelve) (guard : d1866 pattern = 1) : d1799 pattern ≤ (0 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1799, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8097 pattern childGuard
    simpa only [d1799, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1799, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8098 pattern childGuard
    simpa only [d1799, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8100 (pattern : Twelve) (guard : d1866 pattern = 1) : d1782 pattern ≤ (0 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1782, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7766 pattern childGuard
    simpa only [d1782, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1782, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3706 pattern childGuard
    simpa only [d1782, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8101 (pattern : Twelve) (guard : d1866 pattern = 1) : d1785 pattern ≤ (0 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1785, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8100 pattern childGuard
    simpa only [d1785, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1785, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7920 pattern childGuard
    simpa only [d1785, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8102 (pattern : Twelve) (guard : d1866 pattern = 1) : d1793 pattern ≤ (0 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1793, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8047 pattern childGuard
    simpa only [d1793, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1793, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8101 pattern childGuard
    simpa only [d1793, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8103 (pattern : Twelve) (guard : d1866 pattern = 1) : d1800 pattern ≤ (0 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1800, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8102 pattern childGuard
    simpa only [d1800, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1800, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4023 pattern childGuard
    simpa only [d1800, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8104 (pattern : Twelve) (guard : d1866 pattern = 1) : d1805 pattern ≤ (0 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1805, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8099 pattern childGuard
    simpa only [d1805, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1805, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8103 pattern childGuard
    simpa only [d1805, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8105 (pattern : Twelve) (guard : d1866 pattern = 1) : d1806 pattern ≤ (0 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1806, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8095 pattern childGuard
    simpa only [d1806, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1806, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3688 pattern childGuard
    simpa only [d1806, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8106 (pattern : Twelve) (guard : d1866 pattern = 1) : d1809 pattern ≤ (0 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1809, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8104 pattern childGuard
    simpa only [d1809, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1809, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8105 pattern childGuard
    simpa only [d1809, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8107 (pattern : Twelve) (guard : d1866 pattern = 1) : d1811 pattern ≤ (0 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1811, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8096 pattern childGuard
    simpa only [d1811, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1811, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8106 pattern childGuard
    simpa only [d1811, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8108 (pattern : Twelve) (guard : d1866 pattern = 1) : d1794 pattern ≤ (0 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1794, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7753 pattern childGuard
    simpa only [d1794, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1794, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8091 pattern childGuard
    simpa only [d1794, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8109 (pattern : Twelve) (guard : d1866 pattern = 1) : d1801 pattern ≤ (0 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1801, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8108 pattern childGuard
    simpa only [d1801, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1801, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8089 pattern childGuard
    simpa only [d1801, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8110 (pattern : Twelve) (guard : d1866 pattern = 1) : d1807 pattern ≤ (0 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1807, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8109 pattern childGuard
    simpa only [d1807, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1807, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8095 pattern childGuard
    simpa only [d1807, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8111 (pattern : Twelve) (guard : d1866 pattern = 1) : d1783 pattern ≤ (0 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1783, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8057 pattern childGuard
    simpa only [d1783, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1783, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3706 pattern childGuard
    simpa only [d1783, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8112 (pattern : Twelve) (guard : d1866 pattern = 1) : d1786 pattern ≤ (0 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1786, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8091 pattern childGuard
    simpa only [d1786, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1786, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8111 pattern childGuard
    simpa only [d1786, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8113 (pattern : Twelve) (guard : d1866 pattern = 1) : d1795 pattern ≤ (0 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1795, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7935 pattern childGuard
    simpa only [d1795, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1795, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8112 pattern childGuard
    simpa only [d1795, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8114 (pattern : Twelve) (guard : d1866 pattern = 1) : d1802 pattern ≤ (0 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1802, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8113 pattern childGuard
    simpa only [d1802, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1802, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8048 pattern childGuard
    simpa only [d1802, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8115 (pattern : Twelve) (guard : d1866 pattern = 1) : d1787 pattern ≤ (0 : Int) + d1667 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1787, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7920 pattern childGuard
    simpa only [d1787, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1787, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4036 pattern childGuard
    simpa only [d1787, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8116 (pattern : Twelve) (guard : d1866 pattern = 1) : d1796 pattern ≤ (0 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1796, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8047 pattern childGuard
    simpa only [d1796, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1796, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8115 pattern childGuard
    simpa only [d1796, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8117 (pattern : Twelve) (guard : d1866 pattern = 1) : d1803 pattern ≤ (0 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1803, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8116 pattern childGuard
    simpa only [d1803, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1803, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4039 pattern childGuard
    simpa only [d1803, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8118 (pattern : Twelve) (guard : d1866 pattern = 1) : d1808 pattern ≤ (0 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1808, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8114 pattern childGuard
    simpa only [d1808, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1808, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8117 pattern childGuard
    simpa only [d1808, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8119 (pattern : Twelve) (guard : d1866 pattern = 1) : d1810 pattern ≤ (0 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1810, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8118 pattern childGuard
    simpa only [d1810, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1810, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8105 pattern childGuard
    simpa only [d1810, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
