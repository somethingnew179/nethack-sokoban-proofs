/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons009
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c1400 (pattern : Twelve) (guard : d1849 pattern = 1) : d947 pattern ≤ (0 : Int) + d1038 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d947, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1274 pattern childGuard
    simpa only [d947, d1038, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d947, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1399 pattern childGuard
    simpa only [d947, d1038, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1401 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (0 : Int) + d163 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1402 (pattern : Twelve) (guard : d1848 pattern = 1) : d17 pattern ≤ (0 : Int) + d366 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d366, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1401 pattern childGuard
    simpa only [d1848, d366, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1403 (pattern : Twelve) (guard : d0 pattern = 1) : d173 pattern ≤ (0 : Int) + d36 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1404 (pattern : Twelve) (guard : d1849 pattern = 1) : d941 pattern ≤ (0 : Int) + d1031 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d941, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1402 pattern childGuard
    simpa only [d1849, d941, d1031, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d941, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1403 pattern childGuard
    simpa only [d1849, d941, d1031, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1405 (pattern : Twelve) (guard : d1848 pattern = 1) : d817 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d817, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d817, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d817, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d1848, d817, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1406 (pattern : Twelve) (guard : d1849 pattern = 1) : d942 pattern ≤ (0 : Int) + d1032 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d942, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1405 pattern childGuard
    simpa only [d1849, d942, d1032, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d942, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c869 pattern childGuard
    simpa only [d1849, d942, d1032, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1407 (pattern : Twelve) (guard : d1849 pattern = 1) : d948 pattern ≤ (0 : Int) + d1039 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d948, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1404 pattern childGuard
    simpa only [d948, d1039, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d948, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1406 pattern childGuard
    simpa only [d948, d1039, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1408 (pattern : Twelve) (guard : d1849 pattern = 1) : d955 pattern ≤ (0 : Int) + d1048 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d955, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1400 pattern childGuard
    simpa only [d955, d1048, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d955, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1407 pattern childGuard
    simpa only [d955, d1048, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1409 (pattern : Twelve) (guard : d1849 pattern = 1) : d241 pattern ≤ (0 : Int) + d1033 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d241, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d1849, d241, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d241, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c970 pattern childGuard
    simpa only [d1849, d241, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1410 (pattern : Twelve) (guard : d1849 pattern = 1) : d259 pattern ≤ (0 : Int) + d1040 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d259, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1289 pattern childGuard
    simpa only [d259, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d259, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1409 pattern childGuard
    simpa only [d259, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1411 (pattern : Twelve) (guard : d1849 pattern = 1) : d241 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c844 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1412 (pattern : Twelve) (guard : d1849 pattern = 1) : d949 pattern ≤ (0 : Int) + d1041 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d949, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1411 pattern childGuard
    simpa only [d949, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d949, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1406 pattern childGuard
    simpa only [d949, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1413 (pattern : Twelve) (guard : d1849 pattern = 1) : d956 pattern ≤ (0 : Int) + d1049 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d956, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1410 pattern childGuard
    simpa only [d956, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d956, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d956, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1414 (pattern : Twelve) (guard : d1849 pattern = 1) : d963 pattern ≤ (0 : Int) + d1054 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d963, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1408 pattern childGuard
    simpa only [d963, d1054, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d963, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1413 pattern childGuard
    simpa only [d963, d1054, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1415 (pattern : Twelve) (guard : d1848 pattern = 1) : d27 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d27, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d27, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d27, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1356 pattern childGuard
    simpa only [d1848, d27, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1416 (pattern : Twelve) (guard : d1849 pattern = 1) : d943 pattern ≤ (0 : Int) + d1033 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d943, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1415 pattern childGuard
    simpa only [d1849, d943, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d943, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c970 pattern childGuard
    simpa only [d1849, d943, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1417 (pattern : Twelve) (guard : d1849 pattern = 1) : d950 pattern ≤ (0 : Int) + d1040 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d950, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1305 pattern childGuard
    simpa only [d950, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d950, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1416 pattern childGuard
    simpa only [d950, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1418 (pattern : Twelve) (guard : d1848 pattern = 1) : d17 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c259 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1419 (pattern : Twelve) (guard : d1849 pattern = 1) : d944 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1418 pattern childGuard
    simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c844 pattern childGuard
    simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1420 (pattern : Twelve) (guard : d1849 pattern = 1) : d951 pattern ≤ (0 : Int) + d1041 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d951, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1419 pattern childGuard
    simpa only [d951, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d951, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1406 pattern childGuard
    simpa only [d951, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1421 (pattern : Twelve) (guard : d1849 pattern = 1) : d957 pattern ≤ (0 : Int) + d1049 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d957, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1417 pattern childGuard
    simpa only [d957, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d957, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1420 pattern childGuard
    simpa only [d957, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1422 (pattern : Twelve) (guard : d1849 pattern = 1) : d263 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d263, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1315 pattern childGuard
    simpa only [d263, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d263, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1409 pattern childGuard
    simpa only [d263, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1423 (pattern : Twelve) (guard : d1849 pattern = 1) : d958 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d958, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1422 pattern childGuard
    simpa only [d958, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d958, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d958, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1424 (pattern : Twelve) (guard : d1849 pattern = 1) : d964 pattern ≤ (0 : Int) + d1055 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d964, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1421 pattern childGuard
    simpa only [d964, d1055, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d964, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1423 pattern childGuard
    simpa only [d964, d1055, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1425 (pattern : Twelve) (guard : d1849 pattern = 1) : d970 pattern ≤ (0 : Int) + d1060 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d970, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1414 pattern childGuard
    simpa only [d970, d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d970, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1424 pattern childGuard
    simpa only [d970, d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1426 (pattern : Twelve) (guard : d1849 pattern = 1) : d265 pattern ≤ (0 : Int) + d1043 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d265, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1330 pattern childGuard
    simpa only [d265, d1043, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d265, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1409 pattern childGuard
    simpa only [d265, d1043, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1427 (pattern : Twelve) (guard : d1849 pattern = 1) : d959 pattern ≤ (0 : Int) + d1051 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d959, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1426 pattern childGuard
    simpa only [d959, d1051, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d959, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d959, d1051, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1428 (pattern : Twelve) (guard : d1849 pattern = 1) : d251 pattern ≤ (0 : Int) + d1034 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d251, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1342 pattern childGuard
    simpa only [d1849, d251, d1034, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d251, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c995 pattern childGuard
    simpa only [d1849, d251, d1034, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1429 (pattern : Twelve) (guard : d1849 pattern = 1) : d267 pattern ≤ (0 : Int) + d1044 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d267, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1339 pattern childGuard
    simpa only [d267, d1044, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d267, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1428 pattern childGuard
    simpa only [d267, d1044, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1430 (pattern : Twelve) (guard : d1849 pattern = 1) : d251 pattern ≤ (0 : Int) + d40 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1342 pattern childGuard
    simpa only [d1849, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c864 pattern childGuard
    simpa only [d1849, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1431 (pattern : Twelve) (guard : d0 pattern = 1) : d21 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1432 (pattern : Twelve) (guard : d1848 pattern = 1) : d821 pattern ≤ (0 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c392 pattern childGuard
    simpa only [d1848, d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1431 pattern childGuard
    simpa only [d1848, d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1433 (pattern : Twelve) (guard : d1849 pattern = 1) : d945 pattern ≤ (0 : Int) + d1035 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d945, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1432 pattern childGuard
    simpa only [d1849, d945, d1035, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d945, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c999 pattern childGuard
    simpa only [d1849, d945, d1035, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1434 (pattern : Twelve) (guard : d1849 pattern = 1) : d952 pattern ≤ (0 : Int) + d1045 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d952, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1430 pattern childGuard
    simpa only [d952, d1045, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d952, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1433 pattern childGuard
    simpa only [d952, d1045, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1435 (pattern : Twelve) (guard : d1849 pattern = 1) : d960 pattern ≤ (0 : Int) + d1052 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d960, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1429 pattern childGuard
    simpa only [d960, d1052, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d960, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1434 pattern childGuard
    simpa only [d960, d1052, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1436 (pattern : Twelve) (guard : d1849 pattern = 1) : d965 pattern ≤ (0 : Int) + d1056 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d965, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1427 pattern childGuard
    simpa only [d965, d1056, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d965, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1435 pattern childGuard
    simpa only [d965, d1056, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1437 (pattern : Twelve) (guard : d1849 pattern = 1) : d966 pattern ≤ (0 : Int) + d1057 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d966, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1423 pattern childGuard
    simpa only [d966, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d966, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d966, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1438 (pattern : Twelve) (guard : d1849 pattern = 1) : d971 pattern ≤ (0 : Int) + d1061 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d971, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1436 pattern childGuard
    simpa only [d971, d1061, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d971, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1437 pattern childGuard
    simpa only [d971, d1061, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1439 (pattern : Twelve) (guard : d1849 pattern = 1) : d973 pattern ≤ (0 : Int) + d1064 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d973, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1425 pattern childGuard
    simpa only [d973, d1064, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d973, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1438 pattern childGuard
    simpa only [d973, d1064, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1440 (pattern : Twelve) (guard : d1849 pattern = 1) : d953 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d953, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1355 pattern childGuard
    simpa only [d953, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d953, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1416 pattern childGuard
    simpa only [d953, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1441 (pattern : Twelve) (guard : d1848 pattern = 1) : d823 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d823, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d823, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d823, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1311 pattern childGuard
    simpa only [d1848, d823, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1442 (pattern : Twelve) (guard : d1849 pattern = 1) : d946 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1441 pattern childGuard
    simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c844 pattern childGuard
    simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1443 (pattern : Twelve) (guard : d1849 pattern = 1) : d954 pattern ≤ (0 : Int) + d1041 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d954, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1442 pattern childGuard
    simpa only [d954, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d954, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1406 pattern childGuard
    simpa only [d954, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1444 (pattern : Twelve) (guard : d1849 pattern = 1) : d961 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d961, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1440 pattern childGuard
    simpa only [d961, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d961, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1443 pattern childGuard
    simpa only [d961, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1445 (pattern : Twelve) (guard : d1849 pattern = 1) : d967 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1444 pattern childGuard
    simpa only [d967, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1423 pattern childGuard
    simpa only [d967, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1446 (pattern : Twelve) (guard : d1849 pattern = 1) : d968 pattern ≤ (0 : Int) + d1058 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d968, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1423 pattern childGuard
    simpa only [d968, d1058, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d968, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1435 pattern childGuard
    simpa only [d968, d1058, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1447 (pattern : Twelve) (guard : d1849 pattern = 1) : d972 pattern ≤ (0 : Int) + d1062 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d972, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1446 pattern childGuard
    simpa only [d972, d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d972, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1437 pattern childGuard
    simpa only [d972, d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1448 (pattern : Twelve) (guard : d1849 pattern = 1) : d974 pattern ≤ (0 : Int) + d1065 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d974, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1445 pattern childGuard
    simpa only [d974, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d974, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1447 pattern childGuard
    simpa only [d974, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1449 (pattern : Twelve) (guard : d1849 pattern = 1) : d976 pattern ≤ (0 : Int) + d1067 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d976, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1439 pattern childGuard
    simpa only [d976, d1067, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d976, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1448 pattern childGuard
    simpa only [d976, d1067, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1450 (pattern : Twelve) (guard : d1849 pattern = 1) : d962 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d962, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1440 pattern childGuard
    simpa only [d962, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d962, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1420 pattern childGuard
    simpa only [d962, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1451 (pattern : Twelve) (guard : d1849 pattern = 1) : d969 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1450 pattern childGuard
    simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1423 pattern childGuard
    simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1452 (pattern : Twelve) (guard : d1849 pattern = 1) : d975 pattern ≤ (0 : Int) + d1065 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d975, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1451 pattern childGuard
    simpa only [d975, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d975, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1447 pattern childGuard
    simpa only [d975, d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1453 (pattern : Twelve) (guard : d1849 pattern = 1) : d977 pattern ≤ (0 : Int) + d1065 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1452 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1448 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1454 (pattern : Twelve) (guard : d1849 pattern = 1) : d978 pattern ≤ (0 : Int) + d1068 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d978, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1449 pattern childGuard
    simpa only [d978, d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d978, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1453 pattern childGuard
    simpa only [d978, d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1455 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d880 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1456 (pattern : Twelve) (guard : d1849 pattern = 1) : d251 pattern ≤ (0 : Int) + d1036 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d251, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1342 pattern childGuard
    simpa only [d1849, d251, d1036, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d251, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1455 pattern childGuard
    simpa only [d1849, d251, d1036, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1457 (pattern : Twelve) (guard : d1849 pattern = 1) : d267 pattern ≤ (0 : Int) + d1046 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d267, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1339 pattern childGuard
    simpa only [d267, d1046, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d267, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1456 pattern childGuard
    simpa only [d267, d1046, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1458 (pattern : Twelve) (guard : d1849 pattern = 1) : d251 pattern ≤ (0 : Int) + d1037 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d251, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1342 pattern childGuard
    simpa only [d1849, d251, d1037, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d251, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1068 pattern childGuard
    simpa only [d1849, d251, d1037, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1459 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1460 (pattern : Twelve) (guard : d1849 pattern = 1) : d945 pattern ≤ (0 : Int) + d889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d945, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1432 pattern childGuard
    simpa only [d1849, d945, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d945, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1849, d945, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1461 (pattern : Twelve) (guard : d1849 pattern = 1) : d952 pattern ≤ (0 : Int) + d1047 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d952, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1458 pattern childGuard
    simpa only [d952, d1047, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d952, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1460 pattern childGuard
    simpa only [d952, d1047, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1462 (pattern : Twelve) (guard : d1849 pattern = 1) : d960 pattern ≤ (0 : Int) + d1053 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d960, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1457 pattern childGuard
    simpa only [d960, d1053, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d960, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1461 pattern childGuard
    simpa only [d960, d1053, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1463 (pattern : Twelve) (guard : d1849 pattern = 1) : d968 pattern ≤ (0 : Int) + d1059 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d968, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1423 pattern childGuard
    simpa only [d968, d1059, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d968, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1462 pattern childGuard
    simpa only [d968, d1059, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1464 (pattern : Twelve) (guard : d1849 pattern = 1) : d972 pattern ≤ (0 : Int) + d1063 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d972, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1463 pattern childGuard
    simpa only [d972, d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d972, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1437 pattern childGuard
    simpa only [d972, d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1465 (pattern : Twelve) (guard : d1849 pattern = 1) : d975 pattern ≤ (0 : Int) + d1066 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d975, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1451 pattern childGuard
    simpa only [d975, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d975, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1464 pattern childGuard
    simpa only [d975, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1466 (pattern : Twelve) (guard : d1849 pattern = 1) : d974 pattern ≤ (0 : Int) + d1066 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d974, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1445 pattern childGuard
    simpa only [d974, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d974, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1464 pattern childGuard
    simpa only [d974, d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1467 (pattern : Twelve) (guard : d1849 pattern = 1) : d977 pattern ≤ (0 : Int) + d1066 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1465 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1466 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1468 (pattern : Twelve) (guard : d1849 pattern = 1) : d979 pattern ≤ (0 : Int) + d1069 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d979, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1454 pattern childGuard
    simpa only [d979, d1069, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d979, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1467 pattern childGuard
    simpa only [d979, d1069, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1469 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (0 : Int) + d1275 pattern := by
  omega
theorem c1470 (pattern : Twelve) (guard : d1848 pattern = 1) : d1278 pattern ≤ (0 : Int) + d1444 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1278, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d1848, d1278, d1444, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1278, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c325 pattern childGuard
    simpa only [d1848, d1278, d1444, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1471 (pattern : Twelve) (guard : d1849 pattern = 1) : d1380 pattern ≤ (0 : Int) + d1445 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1380, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1470 pattern childGuard
    simpa only [d1849, d1380, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1380, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1050 pattern childGuard
    simpa only [d1849, d1380, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1472 (pattern : Twelve) (guard : d1849 pattern = 1) : d1385 pattern ≤ (0 : Int) + d1448 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1385, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1404 pattern childGuard
    simpa only [d1385, d1448, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1385, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1471 pattern childGuard
    simpa only [d1385, d1448, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1473 (pattern : Twelve) (guard : d1848 pattern = 1) : d19 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c329 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1474 (pattern : Twelve) (guard : d1849 pattern = 1) : d1381 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1473 pattern childGuard
    simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c828 pattern childGuard
    simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1475 (pattern : Twelve) (guard : d1849 pattern = 1) : d1386 pattern ≤ (0 : Int) + d1449 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1386, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1474 pattern childGuard
    simpa only [d1386, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1386, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1386, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1476 (pattern : Twelve) (guard : d1849 pattern = 1) : d1393 pattern ≤ (0 : Int) + d1455 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1393, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1472 pattern childGuard
    simpa only [d1393, d1455, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1393, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1475 pattern childGuard
    simpa only [d1393, d1455, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1477 (pattern : Twelve) (guard : d0 pattern = 1) : d1276 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1478 (pattern : Twelve) (guard : d1848 pattern = 1) : d1279 pattern ≤ (0 : Int) + d1444 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1279, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d1848, d1279, d1444, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1279, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1477 pattern childGuard
    simpa only [d1848, d1279, d1444, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1479 (pattern : Twelve) (guard : d1849 pattern = 1) : d1382 pattern ≤ (0 : Int) + d1445 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1382, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1478 pattern childGuard
    simpa only [d1849, d1382, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1382, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1050 pattern childGuard
    simpa only [d1849, d1382, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1480 (pattern : Twelve) (guard : d1849 pattern = 1) : d1387 pattern ≤ (0 : Int) + d1450 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1387, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1411 pattern childGuard
    simpa only [d1387, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1387, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1479 pattern childGuard
    simpa only [d1387, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1481 (pattern : Twelve) (guard : d1849 pattern = 1) : d942 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1405 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c828 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1482 (pattern : Twelve) (guard : d1849 pattern = 1) : d1388 pattern ≤ (0 : Int) + d1449 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1388, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1481 pattern childGuard
    simpa only [d1388, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1388, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1388, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1483 (pattern : Twelve) (guard : d1849 pattern = 1) : d1394 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1394, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1480 pattern childGuard
    simpa only [d1394, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1394, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1482 pattern childGuard
    simpa only [d1394, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1484 (pattern : Twelve) (guard : d1849 pattern = 1) : d1398 pattern ≤ (0 : Int) + d1459 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1398, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1476 pattern childGuard
    simpa only [d1398, d1459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1398, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1483 pattern childGuard
    simpa only [d1398, d1459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1485 (pattern : Twelve) (guard : d1849 pattern = 1) : d1389 pattern ≤ (0 : Int) + d1450 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1389, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1419 pattern childGuard
    simpa only [d1389, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1389, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1471 pattern childGuard
    simpa only [d1389, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1486 (pattern : Twelve) (guard : d1849 pattern = 1) : d1395 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1395, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1485 pattern childGuard
    simpa only [d1395, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1395, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1475 pattern childGuard
    simpa only [d1395, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1487 (pattern : Twelve) (guard : d1849 pattern = 1) : d1399 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1486 pattern childGuard
    simpa only [d1399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1483 pattern childGuard
    simpa only [d1399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1488 (pattern : Twelve) (guard : d1849 pattern = 1) : d1403 pattern ≤ (0 : Int) + d1463 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1403, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1484 pattern childGuard
    simpa only [d1403, d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1403, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1487 pattern childGuard
    simpa only [d1403, d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1489 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (0 : Int) + d1276 pattern := by
  omega
theorem c1490 (pattern : Twelve) (guard : d0 pattern = 1) : d1277 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1491 (pattern : Twelve) (guard : d1848 pattern = 1) : d1282 pattern ≤ (0 : Int) + d1330 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1282, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1489 pattern childGuard
    simpa only [d1848, d1282, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1282, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1490 pattern childGuard
    simpa only [d1848, d1282, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1492 (pattern : Twelve) (guard : d1849 pattern = 1) : d1383 pattern ≤ (0 : Int) + d1446 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1383, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1491 pattern childGuard
    simpa only [d1849, d1383, d1446, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1383, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1068 pattern childGuard
    simpa only [d1849, d1383, d1446, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1493 (pattern : Twelve) (guard : d1849 pattern = 1) : d1390 pattern ≤ (0 : Int) + d1451 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1390, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1430 pattern childGuard
    simpa only [d1390, d1451, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1390, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1492 pattern childGuard
    simpa only [d1390, d1451, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1494 (pattern : Twelve) (guard : d1849 pattern = 1) : d945 pattern ≤ (0 : Int) + d42 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1432 pattern childGuard
    simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c869 pattern childGuard
    simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1495 (pattern : Twelve) (guard : d1849 pattern = 1) : d1391 pattern ≤ (0 : Int) + d1452 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1391, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1494 pattern childGuard
    simpa only [d1391, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1391, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1391, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1496 (pattern : Twelve) (guard : d1849 pattern = 1) : d1396 pattern ≤ (0 : Int) + d1457 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1396, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1493 pattern childGuard
    simpa only [d1396, d1457, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1396, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1495 pattern childGuard
    simpa only [d1396, d1457, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1497 (pattern : Twelve) (guard : d1849 pattern = 1) : d1400 pattern ≤ (0 : Int) + d1460 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1400, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1483 pattern childGuard
    simpa only [d1400, d1460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1400, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1496 pattern childGuard
    simpa only [d1400, d1460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1498 (pattern : Twelve) (guard : d1849 pattern = 1) : d1401 pattern ≤ (0 : Int) + d1461 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1401, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1483 pattern childGuard
    simpa only [d1401, d1461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1401, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1401, d1461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1499 (pattern : Twelve) (guard : d1849 pattern = 1) : d1404 pattern ≤ (0 : Int) + d1464 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1404, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1497 pattern childGuard
    simpa only [d1404, d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1404, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1498 pattern childGuard
    simpa only [d1404, d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1500 (pattern : Twelve) (guard : d1849 pattern = 1) : d1405 pattern ≤ (0 : Int) + d1466 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1405, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1488 pattern childGuard
    simpa only [d1405, d1466, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1405, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1499 pattern childGuard
    simpa only [d1405, d1466, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1501 (pattern : Twelve) (guard : d1848 pattern = 1) : d1283 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1283, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d1283, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1283, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1290 pattern childGuard
    simpa only [d1848, d1283, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1502 (pattern : Twelve) (guard : d1849 pattern = 1) : d1384 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1501 pattern childGuard
    simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c828 pattern childGuard
    simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1503 (pattern : Twelve) (guard : d1849 pattern = 1) : d1392 pattern ≤ (0 : Int) + d1449 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1392, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1502 pattern childGuard
    simpa only [d1392, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1392, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1392, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1504 (pattern : Twelve) (guard : d1849 pattern = 1) : d1397 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1397, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1485 pattern childGuard
    simpa only [d1397, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1397, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1503 pattern childGuard
    simpa only [d1397, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1505 (pattern : Twelve) (guard : d1849 pattern = 1) : d1402 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1504 pattern childGuard
    simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1483 pattern childGuard
    simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1506 (pattern : Twelve) (guard : d1849 pattern = 1) : d1406 pattern ≤ (0 : Int) + d1467 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1406, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1505 pattern childGuard
    simpa only [d1406, d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1406, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1499 pattern childGuard
    simpa only [d1406, d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1507 (pattern : Twelve) (guard : d1849 pattern = 1) : d1408 pattern ≤ (0 : Int) + d1469 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1408, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1500 pattern childGuard
    simpa only [d1408, d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1408, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1506 pattern childGuard
    simpa only [d1408, d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1508 (pattern : Twelve) (guard : d1849 pattern = 1) : d1407 pattern ≤ (0 : Int) + d1467 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1407, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1487 pattern childGuard
    simpa only [d1407, d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1407, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1499 pattern childGuard
    simpa only [d1407, d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1509 (pattern : Twelve) (guard : d1849 pattern = 1) : d1409 pattern ≤ (0 : Int) + d1467 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1508 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1506 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1510 (pattern : Twelve) (guard : d1849 pattern = 1) : d1410 pattern ≤ (0 : Int) + d1470 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1410, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1507 pattern childGuard
    simpa only [d1410, d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1410, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1509 pattern childGuard
    simpa only [d1410, d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1511 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1331 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1512 (pattern : Twelve) (guard : d1849 pattern = 1) : d1383 pattern ≤ (0 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1383, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1491 pattern childGuard
    simpa only [d1849, d1383, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1383, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1511 pattern childGuard
    simpa only [d1849, d1383, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1513 (pattern : Twelve) (guard : d1849 pattern = 1) : d1390 pattern ≤ (0 : Int) + d1453 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1390, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1430 pattern childGuard
    simpa only [d1390, d1453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1390, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1512 pattern childGuard
    simpa only [d1390, d1453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1514 (pattern : Twelve) (guard : d1849 pattern = 1) : d945 pattern ≤ (0 : Int) + d1447 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d945, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1432 pattern childGuard
    simpa only [d1849, d945, d1447, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d945, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1121 pattern childGuard
    simpa only [d1849, d945, d1447, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1515 (pattern : Twelve) (guard : d1849 pattern = 1) : d1391 pattern ≤ (0 : Int) + d1454 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1391, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1514 pattern childGuard
    simpa only [d1391, d1454, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1391, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1391, d1454, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1516 (pattern : Twelve) (guard : d1849 pattern = 1) : d1396 pattern ≤ (0 : Int) + d1458 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1396, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1513 pattern childGuard
    simpa only [d1396, d1458, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1396, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1515 pattern childGuard
    simpa only [d1396, d1458, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1517 (pattern : Twelve) (guard : d1849 pattern = 1) : d1400 pattern ≤ (0 : Int) + d1462 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1400, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1483 pattern childGuard
    simpa only [d1400, d1462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1400, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1516 pattern childGuard
    simpa only [d1400, d1462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1518 (pattern : Twelve) (guard : d1849 pattern = 1) : d1404 pattern ≤ (0 : Int) + d1465 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1404, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1517 pattern childGuard
    simpa only [d1404, d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1404, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1498 pattern childGuard
    simpa only [d1404, d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1519 (pattern : Twelve) (guard : d1849 pattern = 1) : d1407 pattern ≤ (0 : Int) + d1468 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1407, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1487 pattern childGuard
    simpa only [d1407, d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1407, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1518 pattern childGuard
    simpa only [d1407, d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1520 (pattern : Twelve) (guard : d1849 pattern = 1) : d1406 pattern ≤ (0 : Int) + d1468 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1406, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1505 pattern childGuard
    simpa only [d1406, d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1406, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1518 pattern childGuard
    simpa only [d1406, d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1521 (pattern : Twelve) (guard : d1849 pattern = 1) : d1409 pattern ≤ (0 : Int) + d1468 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1519 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1520 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1522 (pattern : Twelve) (guard : d1849 pattern = 1) : d1411 pattern ≤ (0 : Int) + d1471 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1411, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1510 pattern childGuard
    simpa only [d1411, d1471, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1411, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1521 pattern childGuard
    simpa only [d1411, d1471, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1523 (pattern : Twelve) (guard : d1848 pattern = 1) : d1324 pattern ≤ (0 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c388 pattern childGuard
    simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c389 pattern childGuard
    simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1524 (pattern : Twelve) (guard : d1849 pattern = 1) : d1689 pattern ≤ (0 : Int) + d1645 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1523 pattern childGuard
    simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1109 pattern childGuard
    simpa only [d1849, d1689, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1525 (pattern : Twelve) (guard : d1849 pattern = 1) : d1693 pattern ≤ (0 : Int) + d1716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1693, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1474 pattern childGuard
    simpa only [d1693, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1693, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1524 pattern childGuard
    simpa only [d1693, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1526 (pattern : Twelve) (guard : d1848 pattern = 1) : d25 pattern ≤ (0 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c392 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1527 (pattern : Twelve) (guard : d1849 pattern = 1) : d1690 pattern ≤ (0 : Int) + d42 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1526 pattern childGuard
    simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c869 pattern childGuard
    simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1528 (pattern : Twelve) (guard : d1849 pattern = 1) : d1694 pattern ≤ (0 : Int) + d1452 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1694, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1527 pattern childGuard
    simpa only [d1694, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1694, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1694, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1529 (pattern : Twelve) (guard : d1849 pattern = 1) : d1697 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1697, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1525 pattern childGuard
    simpa only [d1697, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1697, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1528 pattern childGuard
    simpa only [d1697, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1530 (pattern : Twelve) (guard : d0 pattern = 1) : d20 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1531 (pattern : Twelve) (guard : d1848 pattern = 1) : d1644 pattern ≤ (0 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1644, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c388 pattern childGuard
    simpa only [d1848, d1644, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1644, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1530 pattern childGuard
    simpa only [d1848, d1644, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1532 (pattern : Twelve) (guard : d1849 pattern = 1) : d1691 pattern ≤ (0 : Int) + d1645 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1531 pattern childGuard
    simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1109 pattern childGuard
    simpa only [d1849, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1533 (pattern : Twelve) (guard : d1849 pattern = 1) : d1695 pattern ≤ (0 : Int) + d1716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1695, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1481 pattern childGuard
    simpa only [d1695, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1695, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1532 pattern childGuard
    simpa only [d1695, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1534 (pattern : Twelve) (guard : d1849 pattern = 1) : d1698 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1698, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1533 pattern childGuard
    simpa only [d1698, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1698, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1495 pattern childGuard
    simpa only [d1698, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1535 (pattern : Twelve) (guard : d1849 pattern = 1) : d1700 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1529 pattern childGuard
    simpa only [d1700, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1534 pattern childGuard
    simpa only [d1700, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1536 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (0 : Int) + d20 pattern := by
  omega
theorem c1537 (pattern : Twelve) (guard : d0 pattern = 1) : d22 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1538 (pattern : Twelve) (guard : d1848 pattern = 1) : d1646 pattern ≤ (0 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1646, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1536 pattern childGuard
    simpa only [d1848, d1646, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1646, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1537 pattern childGuard
    simpa only [d1848, d1646, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1539 (pattern : Twelve) (guard : d1849 pattern = 1) : d1692 pattern ≤ (0 : Int) + d128 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1538 pattern childGuard
    simpa only [d1849, d1692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1121 pattern childGuard
    simpa only [d1849, d1692, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
