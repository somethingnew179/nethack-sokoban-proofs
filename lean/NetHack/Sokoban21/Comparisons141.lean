/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons140
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c19740 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (16 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19738 pattern childGuard
    simpa only [d837, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19739 pattern childGuard
    simpa only [d837, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19741 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (16 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19740 pattern childGuard
    simpa only [d852, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19706 pattern childGuard
    simpa only [d852, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19742 (pattern : Twelve) (guard : d1 pattern = 1) : d860 pattern ≤ (16 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19737 pattern childGuard
    simpa only [d860, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19741 pattern childGuard
    simpa only [d860, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19743 (pattern : Twelve) (guard : d1 pattern = 1) : d1261 pattern ≤ (16 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1261, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19730 pattern childGuard
    simpa only [d1261, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1261, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19742 pattern childGuard
    simpa only [d1261, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19744 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (16 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19589 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19477 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19745 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (16 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19604 pattern childGuard
    simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19744 pattern childGuard
    simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19746 (pattern : Twelve) (guard : d1 pattern = 1) : d780 pattern ≤ (16 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d780, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19555 pattern childGuard
    simpa only [d780, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d780, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19745 pattern childGuard
    simpa only [d780, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19747 (pattern : Twelve) (guard : d1 pattern = 1) : d1250 pattern ≤ (16 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1250, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19734 pattern childGuard
    simpa only [d1250, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1250, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19746 pattern childGuard
    simpa only [d1250, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19748 (pattern : Twelve) (guard : d1 pattern = 1) : d1255 pattern ≤ (16 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1255, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19521 pattern childGuard
    simpa only [d1255, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1255, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19747 pattern childGuard
    simpa only [d1255, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19749 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19609 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19620 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19750 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19610 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19751 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19749 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19750 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19752 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (16 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19727 pattern childGuard
    simpa only [d48, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19751 pattern childGuard
    simpa only [d48, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19753 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (16 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19738 pattern childGuard
    simpa only [d837, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19752 pattern childGuard
    simpa only [d837, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19754 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (16 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19753 pattern childGuard
    simpa only [d852, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19706 pattern childGuard
    simpa only [d852, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19755 (pattern : Twelve) (guard : d1 pattern = 1) : d1259 pattern ≤ (16 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1259, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19748 pattern childGuard
    simpa only [d1259, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1259, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19754 pattern childGuard
    simpa only [d1259, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19756 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19610 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19620 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19757 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19610 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19756 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19758 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (16 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19520 pattern childGuard
    simpa only [d48, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19757 pattern childGuard
    simpa only [d48, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19759 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (16 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19758 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19537 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19760 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (16 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19519 pattern childGuard
    simpa only [d24, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19732 pattern childGuard
    simpa only [d24, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19761 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (16 : Int) + d1330 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19760 pattern childGuard
    simpa only [d49, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d49, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19762 (pattern : Twelve) (guard : d1 pattern = 1) : d781 pattern ≤ (16 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d781, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19745 pattern childGuard
    simpa only [d781, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d781, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d781, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19763 (pattern : Twelve) (guard : d1 pattern = 1) : d1251 pattern ≤ (16 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1251, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19761 pattern childGuard
    simpa only [d1251, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1251, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19762 pattern childGuard
    simpa only [d1251, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19764 (pattern : Twelve) (guard : d1 pattern = 1) : d1256 pattern ≤ (16 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1256, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19759 pattern childGuard
    simpa only [d1256, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1256, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19763 pattern childGuard
    simpa only [d1256, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19765 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (16 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19591 pattern childGuard
    simpa only [d49, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19622 pattern childGuard
    simpa only [d49, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19766 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19751 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19767 (pattern : Twelve) (guard : d1 pattern = 1) : d787 pattern ≤ (16 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19765 pattern childGuard
    simpa only [d787, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19766 pattern childGuard
    simpa only [d787, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19768 (pattern : Twelve) (guard : d1 pattern = 1) : d1252 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19705 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19769 (pattern : Twelve) (guard : d1 pattern = 1) : d1257 pattern ≤ (16 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1257, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19767 pattern childGuard
    simpa only [d1257, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1257, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19768 pattern childGuard
    simpa only [d1257, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19770 (pattern : Twelve) (guard : d1 pattern = 1) : d1260 pattern ≤ (16 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1260, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19764 pattern childGuard
    simpa only [d1260, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1260, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19769 pattern childGuard
    simpa only [d1260, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19771 (pattern : Twelve) (guard : d1 pattern = 1) : d1262 pattern ≤ (16 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1262, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19755 pattern childGuard
    simpa only [d1262, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1262, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19770 pattern childGuard
    simpa only [d1262, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19772 (pattern : Twelve) (guard : d1 pattern = 1) : d1263 pattern ≤ (16 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1263, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19742 pattern childGuard
    simpa only [d1263, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1263, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1263, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19773 (pattern : Twelve) (guard : d1 pattern = 1) : d1264 pattern ≤ (16 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1264, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19771 pattern childGuard
    simpa only [d1264, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1264, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19772 pattern childGuard
    simpa only [d1264, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19774 (pattern : Twelve) (guard : d1 pattern = 1) : d1265 pattern ≤ (16 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1265, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19743 pattern childGuard
    simpa only [d1265, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1265, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19773 pattern childGuard
    simpa only [d1265, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19775 (pattern : Twelve) (guard : d1872 pattern = 1) : d1266 pattern ≤ (16 : Int) + d1353 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1872, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19714 pattern childGuard
    simpa only [d1872, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1872, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19774 pattern childGuard
    simpa only [d1872, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19776 (pattern : Twelve) (guard : d1872 pattern = 1) : d1267 pattern ≤ (16 : Int) + d1354 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1872 pattern = 1 := by simpa only [d1267, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19713 pattern childGuard
    simpa only [d1267, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1872 pattern = 1 := by simpa only [d1267, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19775 pattern childGuard
    simpa only [d1267, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19777 (pattern : Twelve) (guard : d0 pattern = 1) : d1321 pattern ≤ (16 : Int) + d1664 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c19778 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (16 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19644 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19460 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19779 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (16 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19457 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19778 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19780 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (16 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19442 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19456 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19781 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (16 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19780 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19778 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19782 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (16 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19779 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19781 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19783 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (16 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19782 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19781 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19784 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (16 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19458 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19783 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19785 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (16 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19469 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19465 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19786 (pattern : Twelve) (guard : d1 pattern = 1) : d1301 pattern ≤ (16 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19785 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19787 (pattern : Twelve) (guard : d1 pattern = 1) : d1309 pattern ≤ (16 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19784 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19786 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19788 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (16 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19458 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19789 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (16 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19466 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19788 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19790 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (16 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19672 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19479 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19791 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (16 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19464 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19790 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19792 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (16 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19779 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19791 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19793 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (16 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19781 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19794 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (16 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19792 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19793 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19795 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (16 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19789 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19794 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19796 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (16 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19460 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19479 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19797 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (16 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19463 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19477 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19798 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (16 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19796 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19797 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19799 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (16 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19469 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19798 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19800 (pattern : Twelve) (guard : d1 pattern = 1) : d1290 pattern ≤ (16 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19799 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19498 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19801 (pattern : Twelve) (guard : d1 pattern = 1) : d1302 pattern ≤ (16 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19800 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19802 (pattern : Twelve) (guard : d1 pattern = 1) : d1310 pattern ≤ (16 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19795 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19801 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19803 (pattern : Twelve) (guard : d1 pattern = 1) : d1316 pattern ≤ (16 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19787 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19802 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19804 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (16 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19513 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19463 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19805 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (16 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19804 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19790 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19806 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (16 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19781 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19805 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19807 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (16 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19792 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19806 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19808 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (16 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19466 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19807 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19809 (pattern : Twelve) (guard : d1 pattern = 1) : d1291 pattern ≤ (16 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19799 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19542 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19810 (pattern : Twelve) (guard : d1 pattern = 1) : d1303 pattern ≤ (16 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19809 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19811 (pattern : Twelve) (guard : d1 pattern = 1) : d1311 pattern ≤ (16 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19808 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19810 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19812 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (16 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19542 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19498 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19813 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (16 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19540 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19490 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19814 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (16 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19791 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19813 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19815 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (16 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19805 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19816 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (16 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19814 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19815 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19817 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (16 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19812 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19816 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19818 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (16 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19798 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19491 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19819 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (16 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19818 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19543 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19820 (pattern : Twelve) (guard : d1 pattern = 1) : d1304 pattern ≤ (16 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19819 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19821 (pattern : Twelve) (guard : d1 pattern = 1) : d1312 pattern ≤ (16 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19817 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19820 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19822 (pattern : Twelve) (guard : d1 pattern = 1) : d1317 pattern ≤ (16 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19811 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19821 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19823 (pattern : Twelve) (guard : d1 pattern = 1) : d1318 pattern ≤ (16 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19802 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19824 (pattern : Twelve) (guard : d1 pattern = 1) : d1320 pattern ≤ (16 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19822 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19823 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19825 (pattern : Twelve) (guard : d1 pattern = 1) : d1322 pattern ≤ (16 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19803 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19824 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19826 (pattern : Twelve) (guard : d1872 pattern = 1) : d1323 pattern ≤ (16 : Int) + d1664 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1872, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19777 pattern childGuard
    simpa only [d1872, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1872, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19825 pattern childGuard
    simpa only [d1872, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19827 (pattern : Twelve) (guard : d0 pattern = 1) : d1353 pattern ≤ (16 : Int) + d1677 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c19828 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (16 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19531 pattern childGuard
    simpa only [d117, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19526 pattern childGuard
    simpa only [d117, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19829 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (16 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19568 pattern childGuard
    simpa only [d1276, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19828 pattern childGuard
    simpa only [d1276, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19830 (pattern : Twelve) (guard : d1 pattern = 1) : d1616 pattern ≤ (16 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1616, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19829 pattern childGuard
    simpa only [d1616, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1616, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19805 pattern childGuard
    simpa only [d1616, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19831 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (16 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19717 pattern childGuard
    simpa only [d119, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19828 pattern childGuard
    simpa only [d119, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19832 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (16 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19831 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19805 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19833 (pattern : Twelve) (guard : d1 pattern = 1) : d1619 pattern ≤ (16 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19830 pattern childGuard
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19832 pattern childGuard
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19834 (pattern : Twelve) (guard : d1 pattern = 1) : d1622 pattern ≤ (16 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1622, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19569 pattern childGuard
    simpa only [d1622, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1622, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19833 pattern childGuard
    simpa only [d1622, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19835 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (16 : Int) + d25 pattern := by
  omega
theorem c19836 (pattern : Twelve) (guard : d1 pattern = 1) : d1617 pattern ≤ (16 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19835 pattern childGuard
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19591 pattern childGuard
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19837 (pattern : Twelve) (guard : d1 pattern = 1) : d1623 pattern ≤ (16 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1623, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19836 pattern childGuard
    simpa only [d1623, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1623, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1623, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19838 (pattern : Twelve) (guard : d1 pattern = 1) : d1627 pattern ≤ (16 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1627, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19834 pattern childGuard
    simpa only [d1627, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1627, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19837 pattern childGuard
    simpa only [d1627, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19839 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (16 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19569 pattern childGuard
    simpa only [d40, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d40, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19840 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (16 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19738 pattern childGuard
    simpa only [d830, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19839 pattern childGuard
    simpa only [d830, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19841 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (16 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19603 pattern childGuard
    simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d14, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19842 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (16 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19590 pattern childGuard
    simpa only [d1277, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19841 pattern childGuard
    simpa only [d1277, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19843 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (16 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19829 pattern childGuard
    simpa only [d1282, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19842 pattern childGuard
    simpa only [d1282, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19844 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (16 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19831 pattern childGuard
    simpa only [d125, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d125, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19845 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (16 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19843 pattern childGuard
    simpa only [d1288, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19844 pattern childGuard
    simpa only [d1288, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19846 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (16 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19840 pattern childGuard
    simpa only [d1299, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19845 pattern childGuard
    simpa only [d1299, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19847 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (16 : Int) + d821 pattern := by
  omega
theorem c19848 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (16 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19847 pattern childGuard
    simpa only [d1292, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19592 pattern childGuard
    simpa only [d1292, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19849 (pattern : Twelve) (guard : d1 pattern = 1) : d1304 pattern ≤ (16 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19848 pattern childGuard
    simpa only [d1304, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1304, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19850 (pattern : Twelve) (guard : d1 pattern = 1) : d1312 pattern ≤ (16 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19846 pattern childGuard
    simpa only [d1312, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19849 pattern childGuard
    simpa only [d1312, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19851 (pattern : Twelve) (guard : d1 pattern = 1) : d1630 pattern ≤ (16 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1630, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19838 pattern childGuard
    simpa only [d1630, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1630, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19850 pattern childGuard
    simpa only [d1630, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19852 (pattern : Twelve) (guard : d1 pattern = 1) : d118 pattern ≤ (16 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19744 pattern childGuard
    simpa only [d118, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19490 pattern childGuard
    simpa only [d118, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19853 (pattern : Twelve) (guard : d1 pattern = 1) : d1618 pattern ≤ (16 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1618, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19831 pattern childGuard
    simpa only [d1618, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1618, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19852 pattern childGuard
    simpa only [d1618, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19854 (pattern : Twelve) (guard : d1 pattern = 1) : d1620 pattern ≤ (16 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1620, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19843 pattern childGuard
    simpa only [d1620, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1620, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19853 pattern childGuard
    simpa only [d1620, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19855 (pattern : Twelve) (guard : d1 pattern = 1) : d1624 pattern ≤ (16 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1624, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19738 pattern childGuard
    simpa only [d1624, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1624, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19854 pattern childGuard
    simpa only [d1624, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19856 (pattern : Twelve) (guard : d1 pattern = 1) : d1628 pattern ≤ (16 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1628, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19855 pattern childGuard
    simpa only [d1628, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1628, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19849 pattern childGuard
    simpa only [d1628, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19857 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (16 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19750 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19621 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19858 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (16 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19591 pattern childGuard
    simpa only [d49, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19857 pattern childGuard
    simpa only [d49, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19859 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (16 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19858 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19592 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19860 (pattern : Twelve) (guard : d1 pattern = 1) : d1331 pattern ≤ (16 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19842 pattern childGuard
    simpa only [d1331, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1331, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1331, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19861 (pattern : Twelve) (guard : d1 pattern = 1) : d182 pattern ≤ (16 : Int) + d183 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19852 pattern childGuard
    simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d182, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19862 (pattern : Twelve) (guard : d1 pattern = 1) : d1621 pattern ≤ (16 : Int) + d1667 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1621, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19860 pattern childGuard
    simpa only [d1621, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1621, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19861 pattern childGuard
    simpa only [d1621, d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19863 (pattern : Twelve) (guard : d1 pattern = 1) : d1625 pattern ≤ (16 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1625, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19859 pattern childGuard
    simpa only [d1625, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1625, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19862 pattern childGuard
    simpa only [d1625, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19864 (pattern : Twelve) (guard : d1 pattern = 1) : d1626 pattern ≤ (16 : Int) + d1626 pattern := by
  omega
theorem c19865 (pattern : Twelve) (guard : d1 pattern = 1) : d1629 pattern ≤ (16 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1629, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19863 pattern childGuard
    simpa only [d1629, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1629, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19864 pattern childGuard
    simpa only [d1629, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19866 (pattern : Twelve) (guard : d1 pattern = 1) : d1631 pattern ≤ (16 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1631, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19856 pattern childGuard
    simpa only [d1631, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1631, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19865 pattern childGuard
    simpa only [d1631, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19867 (pattern : Twelve) (guard : d1 pattern = 1) : d1632 pattern ≤ (16 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1632, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19850 pattern childGuard
    simpa only [d1632, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1632, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1632, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19868 (pattern : Twelve) (guard : d1 pattern = 1) : d1633 pattern ≤ (16 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1633, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19866 pattern childGuard
    simpa only [d1633, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1633, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19867 pattern childGuard
    simpa only [d1633, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19869 (pattern : Twelve) (guard : d1 pattern = 1) : d1634 pattern ≤ (16 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1634, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19851 pattern childGuard
    simpa only [d1634, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1634, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19868 pattern childGuard
    simpa only [d1634, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19870 (pattern : Twelve) (guard : d1872 pattern = 1) : d1635 pattern ≤ (16 : Int) + d1677 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1872, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19827 pattern childGuard
    simpa only [d1872, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1872, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19869 pattern childGuard
    simpa only [d1872, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19871 (pattern : Twelve) (guard : d1872 pattern = 1) : d1636 pattern ≤ (16 : Int) + d1678 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1872 pattern = 1 := by simpa only [d1636, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19826 pattern childGuard
    simpa only [d1636, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1872 pattern = 1 := by simpa only [d1636, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19870 pattern childGuard
    simpa only [d1636, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19872 (pattern : Twelve) (guard : d0 pattern = 1) : d1664 pattern ≤ (16 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c19873 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19661 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19663 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19874 (pattern : Twelve) (guard : d1 pattern = 1) : d1649 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19662 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19873 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19875 (pattern : Twelve) (guard : d1 pattern = 1) : d1650 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19664 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19876 (pattern : Twelve) (guard : d1 pattern = 1) : d1656 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19874 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19875 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19877 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19662 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19878 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19665 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19877 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19879 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19873 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19481 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
