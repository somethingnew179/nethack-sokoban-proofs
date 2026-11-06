/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons042
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c6020 (pattern : Twelve) (guard : d1864 pattern = 1) : d1065 pattern ≤ (0 : Int) + d1008 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6019 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6012 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6021 (pattern : Twelve) (guard : d1864 pattern = 1) : d1068 pattern ≤ (0 : Int) + d1009 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1068, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6013 pattern childGuard
    simpa only [d1068, d1009, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1068, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6020 pattern childGuard
    simpa only [d1068, d1009, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6022 (pattern : Twelve) (guard : d0 pattern = 1) : d880 pattern ≤ (0 : Int) + d820 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6023 (pattern : Twelve) (guard : d1849 pattern = 1) : d1036 pattern ≤ (0 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1036, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5034 pattern childGuard
    simpa only [d1849, d1036, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1036, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6022 pattern childGuard
    simpa only [d1849, d1036, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6024 (pattern : Twelve) (guard : d1863 pattern = 1) : d1046 pattern ≤ (0 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1046, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1863, d1046, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1046, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6023 pattern childGuard
    simpa only [d1863, d1046, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6025 (pattern : Twelve) (guard : d0 pattern = 1) : d1047 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6026 (pattern : Twelve) (guard : d1864 pattern = 1) : d1053 pattern ≤ (0 : Int) + d985 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1053, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6024 pattern childGuard
    simpa only [d1864, d1053, d985, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1053, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6025 pattern childGuard
    simpa only [d1864, d1053, d985, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6027 (pattern : Twelve) (guard : d1864 pattern = 1) : d1059 pattern ≤ (0 : Int) + d999 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1059, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6016 pattern childGuard
    simpa only [d1059, d999, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1059, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6026 pattern childGuard
    simpa only [d1059, d999, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6028 (pattern : Twelve) (guard : d1864 pattern = 1) : d1063 pattern ≤ (0 : Int) + d1003 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1063, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6027 pattern childGuard
    simpa only [d1063, d1003, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1063, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5991 pattern childGuard
    simpa only [d1063, d1003, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6029 (pattern : Twelve) (guard : d1864 pattern = 1) : d1066 pattern ≤ (0 : Int) + d1006 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1066, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6014 pattern childGuard
    simpa only [d1066, d1006, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1066, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6028 pattern childGuard
    simpa only [d1066, d1006, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6030 (pattern : Twelve) (guard : d0 pattern = 1) : d880 pattern ≤ (0 : Int) + d47 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6031 (pattern : Twelve) (guard : d1849 pattern = 1) : d1036 pattern ≤ (0 : Int) + d836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1036, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5034 pattern childGuard
    simpa only [d1849, d1036, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1036, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6030 pattern childGuard
    simpa only [d1849, d1036, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6032 (pattern : Twelve) (guard : d1863 pattern = 1) : d1046 pattern ≤ (0 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1046, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1863, d1046, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1046, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6031 pattern childGuard
    simpa only [d1863, d1046, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6033 (pattern : Twelve) (guard : d1864 pattern = 1) : d1053 pattern ≤ (0 : Int) + d989 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1053, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6032 pattern childGuard
    simpa only [d1864, d1053, d989, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1053, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6025 pattern childGuard
    simpa only [d1864, d1053, d989, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6034 (pattern : Twelve) (guard : d1864 pattern = 1) : d1059 pattern ≤ (0 : Int) + d996 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1059, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6004 pattern childGuard
    simpa only [d1059, d996, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1059, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6033 pattern childGuard
    simpa only [d1059, d996, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6035 (pattern : Twelve) (guard : d1864 pattern = 1) : d1063 pattern ≤ (0 : Int) + d1002 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1063, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6034 pattern childGuard
    simpa only [d1063, d1002, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1063, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6010 pattern childGuard
    simpa only [d1063, d1002, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6036 (pattern : Twelve) (guard : d1864 pattern = 1) : d1066 pattern ≤ (0 : Int) + d1005 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1066, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6000 pattern childGuard
    simpa only [d1066, d1005, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1066, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6035 pattern childGuard
    simpa only [d1066, d1005, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6037 (pattern : Twelve) (guard : d1864 pattern = 1) : d1066 pattern ≤ (0 : Int) + d1008 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6029 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6036 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6038 (pattern : Twelve) (guard : d1864 pattern = 1) : d1069 pattern ≤ (0 : Int) + d1010 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1069, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6021 pattern childGuard
    simpa only [d1069, d1010, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1069, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6037 pattern childGuard
    simpa only [d1069, d1010, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6039 (pattern : Twelve) (guard : d0 pattern = 1) : d1280 pattern ≤ (0 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6040 (pattern : Twelve) (guard : d1849 pattern = 1) : d1445 pattern ≤ (0 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1445, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5159 pattern childGuard
    simpa only [d1849, d1445, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1445, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6039 pattern childGuard
    simpa only [d1849, d1445, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6041 (pattern : Twelve) (guard : d1863 pattern = 1) : d1448 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1448, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5348 pattern childGuard
    simpa only [d1863, d1448, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1448, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6040 pattern childGuard
    simpa only [d1863, d1448, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6042 (pattern : Twelve) (guard : d0 pattern = 1) : d1449 pattern ≤ (0 : Int) + d1355 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6043 (pattern : Twelve) (guard : d1864 pattern = 1) : d1455 pattern ≤ (0 : Int) + d1412 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1455, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6041 pattern childGuard
    simpa only [d1864, d1455, d1412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1455, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6042 pattern childGuard
    simpa only [d1864, d1455, d1412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6044 (pattern : Twelve) (guard : d1849 pattern = 1) : d1445 pattern ≤ (0 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1445, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5167 pattern childGuard
    simpa only [d1849, d1445, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1445, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2754 pattern childGuard
    simpa only [d1849, d1445, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6045 (pattern : Twelve) (guard : d1863 pattern = 1) : d1450 pattern ≤ (0 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1450, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5355 pattern childGuard
    simpa only [d1863, d1450, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1450, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6044 pattern childGuard
    simpa only [d1863, d1450, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6046 (pattern : Twelve) (guard : d0 pattern = 1) : d1449 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6047 (pattern : Twelve) (guard : d1864 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1413 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1456, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6045 pattern childGuard
    simpa only [d1864, d1456, d1413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1456, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6046 pattern childGuard
    simpa only [d1864, d1456, d1413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6048 (pattern : Twelve) (guard : d1864 pattern = 1) : d1459 pattern ≤ (0 : Int) + d1417 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1459, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6043 pattern childGuard
    simpa only [d1459, d1417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1459, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6047 pattern childGuard
    simpa only [d1459, d1417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6049 (pattern : Twelve) (guard : d1863 pattern = 1) : d1450 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1450, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5109 pattern childGuard
    simpa only [d1863, d1450, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1450, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6040 pattern childGuard
    simpa only [d1863, d1450, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6050 (pattern : Twelve) (guard : d1864 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1414 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1456, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6049 pattern childGuard
    simpa only [d1864, d1456, d1414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1456, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6046 pattern childGuard
    simpa only [d1864, d1456, d1414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6051 (pattern : Twelve) (guard : d1864 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6050 pattern childGuard
    simpa only [d1418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6047 pattern childGuard
    simpa only [d1418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6052 (pattern : Twelve) (guard : d1864 pattern = 1) : d1463 pattern ≤ (0 : Int) + d1421 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1463, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6048 pattern childGuard
    simpa only [d1463, d1421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1463, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6051 pattern childGuard
    simpa only [d1463, d1421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6053 (pattern : Twelve) (guard : d0 pattern = 1) : d1280 pattern ≤ (0 : Int) + d1281 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6054 (pattern : Twelve) (guard : d1849 pattern = 1) : d1445 pattern ≤ (0 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1445, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5167 pattern childGuard
    simpa only [d1849, d1445, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1445, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6053 pattern childGuard
    simpa only [d1849, d1445, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6055 (pattern : Twelve) (guard : d1863 pattern = 1) : d1450 pattern ≤ (0 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1450, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d1863, d1450, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1450, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6054 pattern childGuard
    simpa only [d1863, d1450, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6056 (pattern : Twelve) (guard : d1864 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1415 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1456, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6055 pattern childGuard
    simpa only [d1864, d1456, d1415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1456, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6046 pattern childGuard
    simpa only [d1864, d1456, d1415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6057 (pattern : Twelve) (guard : d1849 pattern = 1) : d1446 pattern ≤ (0 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1446, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5179 pattern childGuard
    simpa only [d1849, d1446, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1446, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2770 pattern childGuard
    simpa only [d1849, d1446, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6058 (pattern : Twelve) (guard : d1863 pattern = 1) : d1451 pattern ≤ (0 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5374 pattern childGuard
    simpa only [d1863, d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6057 pattern childGuard
    simpa only [d1863, d1451, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6059 (pattern : Twelve) (guard : d0 pattern = 1) : d1452 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6060 (pattern : Twelve) (guard : d1864 pattern = 1) : d1457 pattern ≤ (0 : Int) + d1416 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1457, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6058 pattern childGuard
    simpa only [d1864, d1457, d1416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1457, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6059 pattern childGuard
    simpa only [d1864, d1457, d1416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6061 (pattern : Twelve) (guard : d1864 pattern = 1) : d1460 pattern ≤ (0 : Int) + d1419 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1460, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6056 pattern childGuard
    simpa only [d1460, d1419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1460, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6060 pattern childGuard
    simpa only [d1460, d1419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6062 (pattern : Twelve) (guard : d1864 pattern = 1) : d1461 pattern ≤ (0 : Int) + d1420 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1461, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6047 pattern childGuard
    simpa only [d1461, d1420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1461, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2593 pattern childGuard
    simpa only [d1461, d1420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6063 (pattern : Twelve) (guard : d1864 pattern = 1) : d1464 pattern ≤ (0 : Int) + d1422 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1464, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6061 pattern childGuard
    simpa only [d1464, d1422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1464, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6062 pattern childGuard
    simpa only [d1464, d1422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6064 (pattern : Twelve) (guard : d1864 pattern = 1) : d1466 pattern ≤ (0 : Int) + d1423 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1466, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6052 pattern childGuard
    simpa only [d1466, d1423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1466, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6063 pattern childGuard
    simpa only [d1466, d1423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6065 (pattern : Twelve) (guard : d1864 pattern = 1) : d1467 pattern ≤ (0 : Int) + d1424 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1467, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6051 pattern childGuard
    simpa only [d1467, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1467, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6063 pattern childGuard
    simpa only [d1467, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6066 (pattern : Twelve) (guard : d1864 pattern = 1) : d1469 pattern ≤ (0 : Int) + d1425 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1469, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6064 pattern childGuard
    simpa only [d1469, d1425, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1469, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6065 pattern childGuard
    simpa only [d1469, d1425, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6067 (pattern : Twelve) (guard : d1864 pattern = 1) : d1470 pattern ≤ (0 : Int) + d1426 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1470, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6066 pattern childGuard
    simpa only [d1470, d1426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1470, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6065 pattern childGuard
    simpa only [d1470, d1426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6068 (pattern : Twelve) (guard : d0 pattern = 1) : d1331 pattern ≤ (0 : Int) + d125 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6069 (pattern : Twelve) (guard : d1849 pattern = 1) : d1337 pattern ≤ (0 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1337, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5179 pattern childGuard
    simpa only [d1849, d1337, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1337, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6068 pattern childGuard
    simpa only [d1849, d1337, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6070 (pattern : Twelve) (guard : d1863 pattern = 1) : d1453 pattern ≤ (0 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1453, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5374 pattern childGuard
    simpa only [d1863, d1453, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1453, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6069 pattern childGuard
    simpa only [d1863, d1453, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6071 (pattern : Twelve) (guard : d0 pattern = 1) : d1454 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6072 (pattern : Twelve) (guard : d1864 pattern = 1) : d1458 pattern ≤ (0 : Int) + d1416 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1458, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6070 pattern childGuard
    simpa only [d1864, d1458, d1416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1458, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6071 pattern childGuard
    simpa only [d1864, d1458, d1416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6073 (pattern : Twelve) (guard : d1864 pattern = 1) : d1462 pattern ≤ (0 : Int) + d1419 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1462, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6056 pattern childGuard
    simpa only [d1462, d1419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1462, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6072 pattern childGuard
    simpa only [d1462, d1419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6074 (pattern : Twelve) (guard : d1864 pattern = 1) : d1465 pattern ≤ (0 : Int) + d1422 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1465, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6073 pattern childGuard
    simpa only [d1465, d1422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1465, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6062 pattern childGuard
    simpa only [d1465, d1422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6075 (pattern : Twelve) (guard : d1864 pattern = 1) : d1468 pattern ≤ (0 : Int) + d1424 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1468, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6051 pattern childGuard
    simpa only [d1468, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1468, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6074 pattern childGuard
    simpa only [d1468, d1424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6076 (pattern : Twelve) (guard : d1864 pattern = 1) : d1471 pattern ≤ (0 : Int) + d1427 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1471, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6067 pattern childGuard
    simpa only [d1471, d1427, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1471, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6075 pattern childGuard
    simpa only [d1471, d1427, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6077 (pattern : Twelve) (guard : d0 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6078 (pattern : Twelve) (guard : d1849 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5211 pattern childGuard
    simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6077 pattern childGuard
    simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6079 (pattern : Twelve) (guard : d1863 pattern = 1) : d1716 pattern ≤ (0 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1716, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5162 pattern childGuard
    simpa only [d1863, d1716, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1716, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6078 pattern childGuard
    simpa only [d1863, d1716, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6080 (pattern : Twelve) (guard : d1864 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1705 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1719, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6079 pattern childGuard
    simpa only [d1864, d1719, d1705, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1719, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6059 pattern childGuard
    simpa only [d1864, d1719, d1705, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6081 (pattern : Twelve) (guard : d1849 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5219 pattern childGuard
    simpa only [d1849, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2797 pattern childGuard
    simpa only [d1849, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6082 (pattern : Twelve) (guard : d1863 pattern = 1) : d1716 pattern ≤ (0 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1716, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5416 pattern childGuard
    simpa only [d1863, d1716, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1716, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6081 pattern childGuard
    simpa only [d1863, d1716, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6083 (pattern : Twelve) (guard : d1864 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1706 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1719, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6082 pattern childGuard
    simpa only [d1864, d1719, d1706, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1719, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6059 pattern childGuard
    simpa only [d1864, d1719, d1706, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6084 (pattern : Twelve) (guard : d1864 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1709 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6080 pattern childGuard
    simpa only [d1709, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6083 pattern childGuard
    simpa only [d1709, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6085 (pattern : Twelve) (guard : d0 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1644 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6086 (pattern : Twelve) (guard : d1849 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5219 pattern childGuard
    simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6085 pattern childGuard
    simpa only [d1849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6087 (pattern : Twelve) (guard : d1863 pattern = 1) : d1716 pattern ≤ (0 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1716, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5096 pattern childGuard
    simpa only [d1863, d1716, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1716, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6086 pattern childGuard
    simpa only [d1863, d1716, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6088 (pattern : Twelve) (guard : d1864 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1707 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1719, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6087 pattern childGuard
    simpa only [d1864, d1719, d1707, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1719, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6059 pattern childGuard
    simpa only [d1864, d1719, d1707, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6089 (pattern : Twelve) (guard : d1849 pattern = 1) : d128 pattern ≤ (0 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5225 pattern childGuard
    simpa only [d1849, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2808 pattern childGuard
    simpa only [d1849, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6090 (pattern : Twelve) (guard : d1863 pattern = 1) : d1717 pattern ≤ (0 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1717, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5429 pattern childGuard
    simpa only [d1863, d1717, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1717, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6089 pattern childGuard
    simpa only [d1863, d1717, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6091 (pattern : Twelve) (guard : d1864 pattern = 1) : d1720 pattern ≤ (0 : Int) + d1708 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1720, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6090 pattern childGuard
    simpa only [d1864, d1720, d1708, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1720, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c592 pattern childGuard
    simpa only [d1864, d1720, d1708, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6092 (pattern : Twelve) (guard : d1864 pattern = 1) : d1722 pattern ≤ (0 : Int) + d1710 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1722, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6088 pattern childGuard
    simpa only [d1722, d1710, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1722, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6091 pattern childGuard
    simpa only [d1722, d1710, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6093 (pattern : Twelve) (guard : d1864 pattern = 1) : d1723 pattern ≤ (0 : Int) + d1711 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1723, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6083 pattern childGuard
    simpa only [d1723, d1711, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1723, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2593 pattern childGuard
    simpa only [d1723, d1711, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6094 (pattern : Twelve) (guard : d1864 pattern = 1) : d1725 pattern ≤ (0 : Int) + d1712 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1725, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6092 pattern childGuard
    simpa only [d1725, d1712, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1725, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6093 pattern childGuard
    simpa only [d1725, d1712, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6095 (pattern : Twelve) (guard : d1864 pattern = 1) : d1727 pattern ≤ (0 : Int) + d1713 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1727, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6084 pattern childGuard
    simpa only [d1727, d1713, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1727, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6094 pattern childGuard
    simpa only [d1727, d1713, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6096 (pattern : Twelve) (guard : d0 pattern = 1) : d183 pattern ≤ (0 : Int) + d128 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6097 (pattern : Twelve) (guard : d1849 pattern = 1) : d1667 pattern ≤ (0 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1667, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5225 pattern childGuard
    simpa only [d1849, d1667, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1667, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6096 pattern childGuard
    simpa only [d1849, d1667, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6098 (pattern : Twelve) (guard : d1863 pattern = 1) : d1718 pattern ≤ (0 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1863, d1718, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5429 pattern childGuard
    simpa only [d1863, d1718, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1863, d1718, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6097 pattern childGuard
    simpa only [d1863, d1718, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6099 (pattern : Twelve) (guard : d1864 pattern = 1) : d1721 pattern ≤ (0 : Int) + d1708 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1863 pattern = 1 := by simpa only [d1864, d1721, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6098 pattern childGuard
    simpa only [d1864, d1721, d1708, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1864, d1721, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1256 pattern childGuard
    simpa only [d1864, d1721, d1708, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6100 (pattern : Twelve) (guard : d1864 pattern = 1) : d1724 pattern ≤ (0 : Int) + d1710 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1724, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6088 pattern childGuard
    simpa only [d1724, d1710, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1724, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6099 pattern childGuard
    simpa only [d1724, d1710, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6101 (pattern : Twelve) (guard : d1864 pattern = 1) : d1726 pattern ≤ (0 : Int) + d1712 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1726, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6100 pattern childGuard
    simpa only [d1726, d1712, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1726, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6093 pattern childGuard
    simpa only [d1726, d1712, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6102 (pattern : Twelve) (guard : d1864 pattern = 1) : d1728 pattern ≤ (0 : Int) + d1713 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1728, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6084 pattern childGuard
    simpa only [d1728, d1713, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1728, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6101 pattern childGuard
    simpa only [d1728, d1713, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6103 (pattern : Twelve) (guard : d1864 pattern = 1) : d1729 pattern ≤ (0 : Int) + d1713 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6095 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1864 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6102 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6104 (pattern : Twelve) (guard : d0 pattern = 1) : d185 pattern ≤ (0 : Int) + d50 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6105 (pattern : Twelve) (guard : d1852 pattern = 1) : d425 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d425, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d425, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d425, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6104 pattern childGuard
    simpa only [d1852, d425, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6106 (pattern : Twelve) (guard : d0 pattern = 1) : d426 pattern ≤ (0 : Int) + d198 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6107 (pattern : Twelve) (guard : d1858 pattern = 1) : d444 pattern ≤ (0 : Int) + d304 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d444, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6105 pattern childGuard
    simpa only [d1858, d444, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d444, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6106 pattern childGuard
    simpa only [d1858, d444, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6108 (pattern : Twelve) (guard : d0 pattern = 1) : d188 pattern ≤ (0 : Int) + d53 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6109 (pattern : Twelve) (guard : d1852 pattern = 1) : d427 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d427, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2180 pattern childGuard
    simpa only [d1852, d427, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d427, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6108 pattern childGuard
    simpa only [d1852, d427, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6110 (pattern : Twelve) (guard : d0 pattern = 1) : d428 pattern ≤ (0 : Int) + d200 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6111 (pattern : Twelve) (guard : d1858 pattern = 1) : d445 pattern ≤ (0 : Int) + d305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d445, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6109 pattern childGuard
    simpa only [d1858, d445, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d445, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6110 pattern childGuard
    simpa only [d1858, d445, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6112 (pattern : Twelve) (guard : d1858 pattern = 1) : d455 pattern ≤ (0 : Int) + d320 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d455, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6107 pattern childGuard
    simpa only [d455, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d455, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6111 pattern childGuard
    simpa only [d455, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6113 (pattern : Twelve) (guard : d0 pattern = 1) : d188 pattern ≤ (0 : Int) + d50 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6114 (pattern : Twelve) (guard : d1852 pattern = 1) : d429 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d429, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d429, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d429, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6113 pattern childGuard
    simpa only [d1852, d429, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6115 (pattern : Twelve) (guard : d0 pattern = 1) : d430 pattern ≤ (0 : Int) + d200 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6116 (pattern : Twelve) (guard : d1858 pattern = 1) : d446 pattern ≤ (0 : Int) + d306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d446, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6114 pattern childGuard
    simpa only [d1858, d446, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d446, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6115 pattern childGuard
    simpa only [d1858, d446, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6117 (pattern : Twelve) (guard : d0 pattern = 1) : d191 pattern ≤ (0 : Int) + d57 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6118 (pattern : Twelve) (guard : d1852 pattern = 1) : d431 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d431, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d431, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d431, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6117 pattern childGuard
    simpa only [d1852, d431, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6119 (pattern : Twelve) (guard : d0 pattern = 1) : d432 pattern ≤ (0 : Int) + d202 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6120 (pattern : Twelve) (guard : d1858 pattern = 1) : d447 pattern ≤ (0 : Int) + d307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d447, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6118 pattern childGuard
    simpa only [d1858, d447, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d447, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6119 pattern childGuard
    simpa only [d1858, d447, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6121 (pattern : Twelve) (guard : d1858 pattern = 1) : d456 pattern ≤ (0 : Int) + d321 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d456, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6116 pattern childGuard
    simpa only [d456, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d456, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6120 pattern childGuard
    simpa only [d456, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6122 (pattern : Twelve) (guard : d1858 pattern = 1) : d465 pattern ≤ (0 : Int) + d332 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d465, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6112 pattern childGuard
    simpa only [d465, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d465, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6121 pattern childGuard
    simpa only [d465, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6123 (pattern : Twelve) (guard : d0 pattern = 1) : d193 pattern ≤ (0 : Int) + d58 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6124 (pattern : Twelve) (guard : d1852 pattern = 1) : d433 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d433, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d433, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d433, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6123 pattern childGuard
    simpa only [d1852, d433, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6125 (pattern : Twelve) (guard : d0 pattern = 1) : d434 pattern ≤ (0 : Int) + d204 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6126 (pattern : Twelve) (guard : d1858 pattern = 1) : d448 pattern ≤ (0 : Int) + d308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d448, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6124 pattern childGuard
    simpa only [d1858, d448, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d448, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6125 pattern childGuard
    simpa only [d1858, d448, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6127 (pattern : Twelve) (guard : d0 pattern = 1) : d196 pattern ≤ (0 : Int) + d60 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6128 (pattern : Twelve) (guard : d1852 pattern = 1) : d435 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d435, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d435, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d435, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6127 pattern childGuard
    simpa only [d1852, d435, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6129 (pattern : Twelve) (guard : d0 pattern = 1) : d436 pattern ≤ (0 : Int) + d206 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6130 (pattern : Twelve) (guard : d1858 pattern = 1) : d449 pattern ≤ (0 : Int) + d309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d449, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6128 pattern childGuard
    simpa only [d1858, d449, d309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d449, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6129 pattern childGuard
    simpa only [d1858, d449, d309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6131 (pattern : Twelve) (guard : d1858 pattern = 1) : d457 pattern ≤ (0 : Int) + d322 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d457, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6126 pattern childGuard
    simpa only [d457, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d457, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6130 pattern childGuard
    simpa only [d457, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6132 (pattern : Twelve) (guard : d0 pattern = 1) : d196 pattern ≤ (0 : Int) + d57 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6133 (pattern : Twelve) (guard : d1852 pattern = 1) : d437 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d437, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d437, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d437, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6132 pattern childGuard
    simpa only [d1852, d437, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6134 (pattern : Twelve) (guard : d0 pattern = 1) : d432 pattern ≤ (0 : Int) + d206 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6135 (pattern : Twelve) (guard : d1858 pattern = 1) : d450 pattern ≤ (0 : Int) + d310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d450, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6133 pattern childGuard
    simpa only [d1858, d450, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d450, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6134 pattern childGuard
    simpa only [d1858, d450, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6136 (pattern : Twelve) (guard : d1858 pattern = 1) : d458 pattern ≤ (0 : Int) + d323 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d458, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6135 pattern childGuard
    simpa only [d458, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d458, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2211 pattern childGuard
    simpa only [d458, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6137 (pattern : Twelve) (guard : d1858 pattern = 1) : d466 pattern ≤ (0 : Int) + d333 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d466, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6131 pattern childGuard
    simpa only [d466, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d466, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6136 pattern childGuard
    simpa only [d466, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6138 (pattern : Twelve) (guard : d1858 pattern = 1) : d471 pattern ≤ (0 : Int) + d338 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d471, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6122 pattern childGuard
    simpa only [d471, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d471, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6137 pattern childGuard
    simpa only [d471, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6139 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d50 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6140 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d438, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d438, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d438, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6139 pattern childGuard
    simpa only [d1852, d438, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6141 (pattern : Twelve) (guard : d0 pattern = 1) : d438 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6142 (pattern : Twelve) (guard : d1858 pattern = 1) : d438 pattern ≤ (0 : Int) + d311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6140 pattern childGuard
    simpa only [d1858, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6141 pattern childGuard
    simpa only [d1858, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6143 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d62 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6144 (pattern : Twelve) (guard : d1852 pattern = 1) : d439 pattern ≤ (0 : Int) + d83 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d439, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2180 pattern childGuard
    simpa only [d1852, d439, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d439, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6143 pattern childGuard
    simpa only [d1852, d439, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6145 (pattern : Twelve) (guard : d0 pattern = 1) : d440 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6146 (pattern : Twelve) (guard : d1858 pattern = 1) : d451 pattern ≤ (0 : Int) + d312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d451, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6144 pattern childGuard
    simpa only [d1858, d451, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d451, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6145 pattern childGuard
    simpa only [d1858, d451, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6147 (pattern : Twelve) (guard : d1858 pattern = 1) : d459 pattern ≤ (0 : Int) + d324 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d459, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6142 pattern childGuard
    simpa only [d459, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d459, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6146 pattern childGuard
    simpa only [d459, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6148 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d65 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6149 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (0 : Int) + d85 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d432, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d432, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d432, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6148 pattern childGuard
    simpa only [d1852, d432, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6150 (pattern : Twelve) (guard : d0 pattern = 1) : d432 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6151 (pattern : Twelve) (guard : d1858 pattern = 1) : d432 pattern ≤ (0 : Int) + d313 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6149 pattern childGuard
    simpa only [d1858, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6150 pattern childGuard
    simpa only [d1858, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6152 (pattern : Twelve) (guard : d1858 pattern = 1) : d460 pattern ≤ (0 : Int) + d325 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d460, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6142 pattern childGuard
    simpa only [d460, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d460, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6151 pattern childGuard
    simpa only [d460, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6153 (pattern : Twelve) (guard : d1858 pattern = 1) : d467 pattern ≤ (0 : Int) + d334 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d467, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6147 pattern childGuard
    simpa only [d467, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d467, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6152 pattern childGuard
    simpa only [d467, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6154 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d67 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6155 (pattern : Twelve) (guard : d1852 pattern = 1) : d441 pattern ≤ (0 : Int) + d87 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d441, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d441, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d441, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6154 pattern childGuard
    simpa only [d1852, d441, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6156 (pattern : Twelve) (guard : d0 pattern = 1) : d441 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6157 (pattern : Twelve) (guard : d1858 pattern = 1) : d441 pattern ≤ (0 : Int) + d314 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6155 pattern childGuard
    simpa only [d1858, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6156 pattern childGuard
    simpa only [d1858, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6158 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d69 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6159 (pattern : Twelve) (guard : d1852 pattern = 1) : d436 pattern ≤ (0 : Int) + d89 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d436, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d436, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d436, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6158 pattern childGuard
    simpa only [d1852, d436, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
