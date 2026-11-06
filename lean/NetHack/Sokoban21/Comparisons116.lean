/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons115
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c16240 (pattern : Twelve) (guard : d2746 pattern = 1) : d1182 pattern ≤ (1 : Int) + d2857 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1182, d2857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16202 pattern childGuard
    simpa only [d1182, d2857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1182, d2857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16239 pattern childGuard
    simpa only [d1182, d2857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16241 (pattern : Twelve) (guard : d2746 pattern = 1) : d1105 pattern ≤ (1 : Int) + d2830 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d1105, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16138 pattern childGuard
    simpa only [d2746, d1105, d2830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d1105, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11105 pattern childGuard
    simpa only [d2746, d1105, d2830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16242 (pattern : Twelve) (guard : d2746 pattern = 1) : d1108 pattern ≤ (1 : Int) + d2830 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16241 pattern childGuard
    simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16203 pattern childGuard
    simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16243 (pattern : Twelve) (guard : d2746 pattern = 1) : d1505 pattern ≤ (1 : Int) + d2830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16242 pattern childGuard
    simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16203 pattern childGuard
    simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16244 (pattern : Twelve) (guard : d2746 pattern = 1) : d1517 pattern ≤ (1 : Int) + d2858 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1517, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16144 pattern childGuard
    simpa only [d1517, d2858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1517, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16243 pattern childGuard
    simpa only [d1517, d2858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16245 (pattern : Twelve) (guard : d2746 pattern = 1) : d1518 pattern ≤ (1 : Int) + d2859 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1518, d2859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15959 pattern childGuard
    simpa only [d1518, d2859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1518, d2859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1518, d2859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16246 (pattern : Twelve) (guard : d2746 pattern = 1) : d1532 pattern ≤ (1 : Int) + d2860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1532, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16244 pattern childGuard
    simpa only [d1532, d2860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1532, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16245 pattern childGuard
    simpa only [d1532, d2860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16247 (pattern : Twelve) (guard : d2746 pattern = 1) : d1106 pattern ≤ (1 : Int) + d2795 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d1106, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16178 pattern childGuard
    simpa only [d2746, d1106, d2795, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d1106, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11128 pattern childGuard
    simpa only [d2746, d1106, d2795, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16248 (pattern : Twelve) (guard : d2746 pattern = 1) : d1495 pattern ≤ (1 : Int) + d2861 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1495, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16241 pattern childGuard
    simpa only [d1495, d2861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1495, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16247 pattern childGuard
    simpa only [d1495, d2861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16249 (pattern : Twelve) (guard : d2746 pattern = 1) : d1496 pattern ≤ (1 : Int) + d2862 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1496, d2862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16203 pattern childGuard
    simpa only [d1496, d2862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1496, d2862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1496, d2862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16250 (pattern : Twelve) (guard : d2746 pattern = 1) : d1506 pattern ≤ (1 : Int) + d2863 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1506, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16248 pattern childGuard
    simpa only [d1506, d2863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1506, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16249 pattern childGuard
    simpa only [d1506, d2863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16251 (pattern : Twelve) (guard : d2746 pattern = 1) : d1519 pattern ≤ (1 : Int) + d2864 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1519, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16160 pattern childGuard
    simpa only [d1519, d2864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1519, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16250 pattern childGuard
    simpa only [d1519, d2864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16252 (pattern : Twelve) (guard : d2746 pattern = 1) : d1109 pattern ≤ (1 : Int) + d2770 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1109, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15959 pattern childGuard
    simpa only [d1109, d2770, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1109, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16048 pattern childGuard
    simpa only [d1109, d2770, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16253 (pattern : Twelve) (guard : d2746 pattern = 1) : d1507 pattern ≤ (1 : Int) + d2823 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1507, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16252 pattern childGuard
    simpa only [d1507, d2823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1507, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15961 pattern childGuard
    simpa only [d1507, d2823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16254 (pattern : Twelve) (guard : d2746 pattern = 1) : d1520 pattern ≤ (1 : Int) + d2824 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1520, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16253 pattern childGuard
    simpa only [d1520, d2824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1520, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1520, d2824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16255 (pattern : Twelve) (guard : d2746 pattern = 1) : d1533 pattern ≤ (1 : Int) + d2865 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1533, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16251 pattern childGuard
    simpa only [d1533, d2865, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1533, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16254 pattern childGuard
    simpa only [d1533, d2865, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16256 (pattern : Twelve) (guard : d2746 pattern = 1) : d1541 pattern ≤ (1 : Int) + d2866 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1541, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16246 pattern childGuard
    simpa only [d1541, d2866, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1541, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16255 pattern childGuard
    simpa only [d1541, d2866, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16257 (pattern : Twelve) (guard : d2746 pattern = 1) : d1521 pattern ≤ (1 : Int) + d2858 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1521, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d1521, d2858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1521, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16243 pattern childGuard
    simpa only [d1521, d2858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16258 (pattern : Twelve) (guard : d2746 pattern = 1) : d1534 pattern ≤ (1 : Int) + d2860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1534, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16257 pattern childGuard
    simpa only [d1534, d2860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1534, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16245 pattern childGuard
    simpa only [d1534, d2860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16259 (pattern : Twelve) (guard : d2746 pattern = 1) : d1542 pattern ≤ (1 : Int) + d2866 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1542, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16258 pattern childGuard
    simpa only [d1542, d2866, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1542, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16255 pattern childGuard
    simpa only [d1542, d2866, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16260 (pattern : Twelve) (guard : d2746 pattern = 1) : d1548 pattern ≤ (1 : Int) + d2866 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16256 pattern childGuard
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16259 pattern childGuard
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16261 (pattern : Twelve) (guard : d2746 pattern = 1) : d1497 pattern ≤ (1 : Int) + d2861 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1497, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16203 pattern childGuard
    simpa only [d1497, d2861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1497, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16118 pattern childGuard
    simpa only [d1497, d2861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16262 (pattern : Twelve) (guard : d2746 pattern = 1) : d1508 pattern ≤ (1 : Int) + d2861 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16248 pattern childGuard
    simpa only [d1508, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16261 pattern childGuard
    simpa only [d1508, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16263 (pattern : Twelve) (guard : d2746 pattern = 1) : d1522 pattern ≤ (1 : Int) + d2867 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1522, d2867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15990 pattern childGuard
    simpa only [d1522, d2867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1522, d2867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16262 pattern childGuard
    simpa only [d1522, d2867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16264 (pattern : Twelve) (guard : d2746 pattern = 1) : d1523 pattern ≤ (1 : Int) + d2868 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1523, d2868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16252 pattern childGuard
    simpa only [d1523, d2868, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1523, d2868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1523, d2868, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16265 (pattern : Twelve) (guard : d2746 pattern = 1) : d1535 pattern ≤ (1 : Int) + d2869 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1535, d2869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16263 pattern childGuard
    simpa only [d1535, d2869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1535, d2869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16264 pattern childGuard
    simpa only [d1535, d2869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16266 (pattern : Twelve) (guard : d0 pattern = 1) : d4 pattern ≤ (1 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16267 (pattern : Twelve) (guard : d7 pattern = 1) : d15 pattern ≤ (1 : Int) + d5 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16266 pattern childGuard
    simpa only [d7, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11385 pattern childGuard
    simpa only [d7, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16268 (pattern : Twelve) (guard : d2746 pattern = 1) : d1493 pattern ≤ (1 : Int) + d497 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d1493, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16267 pattern childGuard
    simpa only [d2746, d1493, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d1493, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d2746, d1493, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16269 (pattern : Twelve) (guard : d2746 pattern = 1) : d1498 pattern ≤ (1 : Int) + d2870 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1498, d2870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16247 pattern childGuard
    simpa only [d1498, d2870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1498, d2870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16268 pattern childGuard
    simpa only [d1498, d2870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16270 (pattern : Twelve) (guard : d2746 pattern = 1) : d1509 pattern ≤ (1 : Int) + d2871 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1509, d2871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16269 pattern childGuard
    simpa only [d1509, d2871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1509, d2871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16119 pattern childGuard
    simpa only [d1509, d2871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16271 (pattern : Twelve) (guard : d2746 pattern = 1) : d1524 pattern ≤ (1 : Int) + d2872 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1524, d2872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16183 pattern childGuard
    simpa only [d1524, d2872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1524, d2872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16270 pattern childGuard
    simpa only [d1524, d2872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16272 (pattern : Twelve) (guard : d2746 pattern = 1) : d1113 pattern ≤ (1 : Int) + d2771 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1113, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16048 pattern childGuard
    simpa only [d1113, d2771, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1113, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15980 pattern childGuard
    simpa only [d1113, d2771, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16273 (pattern : Twelve) (guard : d2746 pattern = 1) : d1510 pattern ≤ (1 : Int) + d2771 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16272 pattern childGuard
    simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16049 pattern childGuard
    simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16274 (pattern : Twelve) (guard : d2746 pattern = 1) : d1525 pattern ≤ (1 : Int) + d2873 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1525, d2873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16273 pattern childGuard
    simpa only [d1525, d2873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1525, d2873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1525, d2873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16275 (pattern : Twelve) (guard : d2746 pattern = 1) : d1536 pattern ≤ (1 : Int) + d2874 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1536, d2874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16271 pattern childGuard
    simpa only [d1536, d2874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1536, d2874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16274 pattern childGuard
    simpa only [d1536, d2874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16276 (pattern : Twelve) (guard : d2746 pattern = 1) : d1543 pattern ≤ (1 : Int) + d2875 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1543, d2875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16265 pattern childGuard
    simpa only [d1543, d2875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1543, d2875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16275 pattern childGuard
    simpa only [d1543, d2875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16277 (pattern : Twelve) (guard : d2746 pattern = 1) : d1544 pattern ≤ (1 : Int) + d2876 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1544, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16255 pattern childGuard
    simpa only [d1544, d2876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1544, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1544, d2876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16278 (pattern : Twelve) (guard : d2746 pattern = 1) : d1549 pattern ≤ (1 : Int) + d2877 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1549, d2877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16276 pattern childGuard
    simpa only [d1549, d2877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1549, d2877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16277 pattern childGuard
    simpa only [d1549, d2877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16279 (pattern : Twelve) (guard : d2746 pattern = 1) : d1551 pattern ≤ (1 : Int) + d2878 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1551, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16260 pattern childGuard
    simpa only [d1551, d2878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1551, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16278 pattern childGuard
    simpa only [d1551, d2878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16280 (pattern : Twelve) (guard : d2746 pattern = 1) : d1552 pattern ≤ (1 : Int) + d2878 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1552, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16259 pattern childGuard
    simpa only [d1552, d2878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1552, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16278 pattern childGuard
    simpa only [d1552, d2878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16281 (pattern : Twelve) (guard : d2746 pattern = 1) : d1554 pattern ≤ (1 : Int) + d2878 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16279 pattern childGuard
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16280 pattern childGuard
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16282 (pattern : Twelve) (guard : d2746 pattern = 1) : d1555 pattern ≤ (1 : Int) + d2878 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16281 pattern childGuard
    simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16280 pattern childGuard
    simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16283 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (1 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16284 (pattern : Twelve) (guard : d7 pattern = 1) : d11 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16283 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11190 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16285 (pattern : Twelve) (guard : d2746 pattern = 1) : d1494 pattern ≤ (1 : Int) + d2795 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d1494, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16284 pattern childGuard
    simpa only [d2746, d1494, d2795, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d1494, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11128 pattern childGuard
    simpa only [d2746, d1494, d2795, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16286 (pattern : Twelve) (guard : d2746 pattern = 1) : d1499 pattern ≤ (1 : Int) + d2861 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1499, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16241 pattern childGuard
    simpa only [d1499, d2861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1499, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16285 pattern childGuard
    simpa only [d1499, d2861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16287 (pattern : Twelve) (guard : d2746 pattern = 1) : d1500 pattern ≤ (1 : Int) + d2861 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1500, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16203 pattern childGuard
    simpa only [d1500, d2861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1500, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16285 pattern childGuard
    simpa only [d1500, d2861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16288 (pattern : Twelve) (guard : d2746 pattern = 1) : d1511 pattern ≤ (1 : Int) + d2861 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16286 pattern childGuard
    simpa only [d1511, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16287 pattern childGuard
    simpa only [d1511, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16289 (pattern : Twelve) (guard : d2746 pattern = 1) : d1526 pattern ≤ (1 : Int) + d2879 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1526, d2879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d1526, d2879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1526, d2879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16288 pattern childGuard
    simpa only [d1526, d2879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16290 (pattern : Twelve) (guard : d2746 pattern = 1) : d1537 pattern ≤ (1 : Int) + d2880 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1537, d2880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16289 pattern childGuard
    simpa only [d1537, d2880, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1537, d2880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16245 pattern childGuard
    simpa only [d1537, d2880, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16291 (pattern : Twelve) (guard : d2746 pattern = 1) : d1111 pattern ≤ (1 : Int) + d2861 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1111, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16241 pattern childGuard
    simpa only [d1111, d2861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1111, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16118 pattern childGuard
    simpa only [d1111, d2861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16292 (pattern : Twelve) (guard : d2746 pattern = 1) : d1512 pattern ≤ (1 : Int) + d2863 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1512, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16291 pattern childGuard
    simpa only [d1512, d2863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1512, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16249 pattern childGuard
    simpa only [d1512, d2863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16293 (pattern : Twelve) (guard : d2746 pattern = 1) : d1527 pattern ≤ (1 : Int) + d2864 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1527, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16160 pattern childGuard
    simpa only [d1527, d2864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1527, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16292 pattern childGuard
    simpa only [d1527, d2864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16294 (pattern : Twelve) (guard : d2746 pattern = 1) : d1538 pattern ≤ (1 : Int) + d2865 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1538, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16293 pattern childGuard
    simpa only [d1538, d2865, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1538, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16254 pattern childGuard
    simpa only [d1538, d2865, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16295 (pattern : Twelve) (guard : d2746 pattern = 1) : d1545 pattern ≤ (1 : Int) + d2881 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1545, d2881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16290 pattern childGuard
    simpa only [d1545, d2881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1545, d2881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16294 pattern childGuard
    simpa only [d1545, d2881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16296 (pattern : Twelve) (guard : d2746 pattern = 1) : d1501 pattern ≤ (1 : Int) + d2882 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1501, d2882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16203 pattern childGuard
    simpa only [d1501, d2882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1501, d2882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16268 pattern childGuard
    simpa only [d1501, d2882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16297 (pattern : Twelve) (guard : d2746 pattern = 1) : d1513 pattern ≤ (1 : Int) + d2883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1513, d2883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16291 pattern childGuard
    simpa only [d1513, d2883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1513, d2883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16296 pattern childGuard
    simpa only [d1513, d2883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16298 (pattern : Twelve) (guard : d2746 pattern = 1) : d1528 pattern ≤ (1 : Int) + d2884 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1528, d2884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15990 pattern childGuard
    simpa only [d1528, d2884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1528, d2884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16297 pattern childGuard
    simpa only [d1528, d2884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16299 (pattern : Twelve) (guard : d2746 pattern = 1) : d1502 pattern ≤ (1 : Int) + d2752 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1502, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15959 pattern childGuard
    simpa only [d1502, d2752, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1502, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15972 pattern childGuard
    simpa only [d1502, d2752, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16300 (pattern : Twelve) (guard : d2746 pattern = 1) : d1514 pattern ≤ (1 : Int) + d2823 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1514, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16252 pattern childGuard
    simpa only [d1514, d2823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1514, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16299 pattern childGuard
    simpa only [d1514, d2823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16301 (pattern : Twelve) (guard : d2746 pattern = 1) : d1529 pattern ≤ (1 : Int) + d2824 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1529, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16300 pattern childGuard
    simpa only [d1529, d2824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1529, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1529, d2824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16302 (pattern : Twelve) (guard : d2746 pattern = 1) : d1539 pattern ≤ (1 : Int) + d2885 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1539, d2885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16298 pattern childGuard
    simpa only [d1539, d2885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1539, d2885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16301 pattern childGuard
    simpa only [d1539, d2885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16303 (pattern : Twelve) (guard : d2746 pattern = 1) : d1112 pattern ≤ (1 : Int) + d2796 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1112, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16247 pattern childGuard
    simpa only [d1112, d2796, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1112, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1112, d2796, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16304 (pattern : Twelve) (guard : d2746 pattern = 1) : d1503 pattern ≤ (1 : Int) + d2886 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1503, d2886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16268 pattern childGuard
    simpa only [d1503, d2886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1503, d2886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1503, d2886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16305 (pattern : Twelve) (guard : d2746 pattern = 1) : d1515 pattern ≤ (1 : Int) + d2887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1515, d2887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16303 pattern childGuard
    simpa only [d1515, d2887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1515, d2887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16304 pattern childGuard
    simpa only [d1515, d2887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16306 (pattern : Twelve) (guard : d2746 pattern = 1) : d1530 pattern ≤ (1 : Int) + d2888 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1530, d2888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16183 pattern childGuard
    simpa only [d1530, d2888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1530, d2888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16305 pattern childGuard
    simpa only [d1530, d2888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16307 (pattern : Twelve) (guard : d2746 pattern = 1) : d1504 pattern ≤ (1 : Int) + d2771 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1504, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16048 pattern childGuard
    simpa only [d1504, d2771, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1504, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15986 pattern childGuard
    simpa only [d1504, d2771, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16308 (pattern : Twelve) (guard : d2746 pattern = 1) : d1516 pattern ≤ (1 : Int) + d2889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1516, d2889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16307 pattern childGuard
    simpa only [d1516, d2889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1516, d2889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16128 pattern childGuard
    simpa only [d1516, d2889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16309 (pattern : Twelve) (guard : d2746 pattern = 1) : d1531 pattern ≤ (1 : Int) + d2890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1531, d2890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16308 pattern childGuard
    simpa only [d1531, d2890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1531, d2890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1531, d2890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16310 (pattern : Twelve) (guard : d2746 pattern = 1) : d1540 pattern ≤ (1 : Int) + d2891 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1540, d2891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16306 pattern childGuard
    simpa only [d1540, d2891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1540, d2891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16309 pattern childGuard
    simpa only [d1540, d2891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16311 (pattern : Twelve) (guard : d2746 pattern = 1) : d1546 pattern ≤ (1 : Int) + d2892 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1546, d2892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16302 pattern childGuard
    simpa only [d1546, d2892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1546, d2892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16310 pattern childGuard
    simpa only [d1546, d2892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16312 (pattern : Twelve) (guard : d2746 pattern = 1) : d1547 pattern ≤ (1 : Int) + d2876 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1547, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16294 pattern childGuard
    simpa only [d1547, d2876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1547, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1547, d2876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16313 (pattern : Twelve) (guard : d2746 pattern = 1) : d1550 pattern ≤ (1 : Int) + d2893 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1550, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16311 pattern childGuard
    simpa only [d1550, d2893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1550, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16312 pattern childGuard
    simpa only [d1550, d2893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16314 (pattern : Twelve) (guard : d2746 pattern = 1) : d1553 pattern ≤ (1 : Int) + d2894 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1553, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16295 pattern childGuard
    simpa only [d1553, d2894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1553, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16313 pattern childGuard
    simpa only [d1553, d2894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16315 (pattern : Twelve) (guard : d2746 pattern = 1) : d1556 pattern ≤ (1 : Int) + d2895 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1556, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16282 pattern childGuard
    simpa only [d1556, d2895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1556, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16314 pattern childGuard
    simpa only [d1556, d2895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16316 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16317 (pattern : Twelve) (guard : d7 pattern = 1) : d11 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16316 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11233 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16318 (pattern : Twelve) (guard : d2746 pattern = 1) : d1494 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16317 pattern childGuard
    simpa only [d2746, d1494, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d2746, d1494, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16319 (pattern : Twelve) (guard : d2746 pattern = 1) : d1753 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16147 pattern childGuard
    simpa only [d1753, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16318 pattern childGuard
    simpa only [d1753, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16320 (pattern : Twelve) (guard : d2746 pattern = 1) : d1754 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16150 pattern childGuard
    simpa only [d1754, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1754, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16321 (pattern : Twelve) (guard : d2746 pattern = 1) : d1763 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16319 pattern childGuard
    simpa only [d1763, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16320 pattern childGuard
    simpa only [d1763, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16322 (pattern : Twelve) (guard : d2746 pattern = 1) : d503 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16147 pattern childGuard
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16323 (pattern : Twelve) (guard : d2746 pattern = 1) : d1507 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16151 pattern childGuard
    simpa only [d1507, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16322 pattern childGuard
    simpa only [d1507, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16324 (pattern : Twelve) (guard : d2746 pattern = 1) : d1745 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16318 pattern childGuard
    simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15972 pattern childGuard
    simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16325 (pattern : Twelve) (guard : d2746 pattern = 1) : d1746 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16318 pattern childGuard
    simpa only [d1746, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1746, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16326 (pattern : Twelve) (guard : d2746 pattern = 1) : d1749 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16324 pattern childGuard
    simpa only [d1749, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16325 pattern childGuard
    simpa only [d1749, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16327 (pattern : Twelve) (guard : d2746 pattern = 1) : d1755 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16323 pattern childGuard
    simpa only [d1755, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16326 pattern childGuard
    simpa only [d1755, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16328 (pattern : Twelve) (guard : d2746 pattern = 1) : d1510 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16184 pattern childGuard
    simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16152 pattern childGuard
    simpa only [d1510, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16329 (pattern : Twelve) (guard : d2746 pattern = 1) : d1525 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16328 pattern childGuard
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16330 (pattern : Twelve) (guard : d2746 pattern = 1) : d1764 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16327 pattern childGuard
    simpa only [d1764, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16329 pattern childGuard
    simpa only [d1764, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16331 (pattern : Twelve) (guard : d2746 pattern = 1) : d1770 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16321 pattern childGuard
    simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16330 pattern childGuard
    simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16332 (pattern : Twelve) (guard : d2746 pattern = 1) : d1756 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16151 pattern childGuard
    simpa only [d1756, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16324 pattern childGuard
    simpa only [d1756, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16333 (pattern : Twelve) (guard : d2746 pattern = 1) : d1757 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16184 pattern childGuard
    simpa only [d1757, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1757, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16334 (pattern : Twelve) (guard : d2746 pattern = 1) : d1765 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16332 pattern childGuard
    simpa only [d1765, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16333 pattern childGuard
    simpa only [d1765, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16335 (pattern : Twelve) (guard : d2746 pattern = 1) : d1747 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15972 pattern childGuard
    simpa only [d1747, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15986 pattern childGuard
    simpa only [d1747, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16336 (pattern : Twelve) (guard : d2746 pattern = 1) : d1750 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16335 pattern childGuard
    simpa only [d1750, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16128 pattern childGuard
    simpa only [d1750, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16337 (pattern : Twelve) (guard : d2746 pattern = 1) : d1758 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16328 pattern childGuard
    simpa only [d1758, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16336 pattern childGuard
    simpa only [d1758, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16338 (pattern : Twelve) (guard : d2746 pattern = 1) : d1759 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16185 pattern childGuard
    simpa only [d1759, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1759, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16339 (pattern : Twelve) (guard : d2746 pattern = 1) : d1766 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16337 pattern childGuard
    simpa only [d1766, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16338 pattern childGuard
    simpa only [d1766, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16340 (pattern : Twelve) (guard : d2746 pattern = 1) : d1771 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16334 pattern childGuard
    simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16339 pattern childGuard
    simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16341 (pattern : Twelve) (guard : d2746 pattern = 1) : d1772 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16330 pattern childGuard
    simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16342 (pattern : Twelve) (guard : d2746 pattern = 1) : d1775 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16340 pattern childGuard
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16341 pattern childGuard
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16343 (pattern : Twelve) (guard : d2746 pattern = 1) : d1777 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16331 pattern childGuard
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16342 pattern childGuard
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16344 (pattern : Twelve) (guard : d2746 pattern = 1) : d1760 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16147 pattern childGuard
    simpa only [d1760, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16324 pattern childGuard
    simpa only [d1760, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16345 (pattern : Twelve) (guard : d2746 pattern = 1) : d1767 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16344 pattern childGuard
    simpa only [d1767, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16320 pattern childGuard
    simpa only [d1767, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16346 (pattern : Twelve) (guard : d2746 pattern = 1) : d1773 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16345 pattern childGuard
    simpa only [d1773, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16330 pattern childGuard
    simpa only [d1773, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16347 (pattern : Twelve) (guard : d2746 pattern = 1) : d1748 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16318 pattern childGuard
    simpa only [d1748, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15986 pattern childGuard
    simpa only [d1748, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16348 (pattern : Twelve) (guard : d2746 pattern = 1) : d1751 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16324 pattern childGuard
    simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16347 pattern childGuard
    simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16349 (pattern : Twelve) (guard : d2746 pattern = 1) : d1761 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16151 pattern childGuard
    simpa only [d1761, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16348 pattern childGuard
    simpa only [d1761, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16350 (pattern : Twelve) (guard : d2746 pattern = 1) : d1768 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16349 pattern childGuard
    simpa only [d1768, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16329 pattern childGuard
    simpa only [d1768, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16351 (pattern : Twelve) (guard : d2746 pattern = 1) : d183 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15986 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16352 (pattern : Twelve) (guard : d2746 pattern = 1) : d1752 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16128 pattern childGuard
    simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16351 pattern childGuard
    simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16353 (pattern : Twelve) (guard : d2746 pattern = 1) : d1762 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16328 pattern childGuard
    simpa only [d1762, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16352 pattern childGuard
    simpa only [d1762, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16354 (pattern : Twelve) (guard : d2746 pattern = 1) : d191 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16185 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16355 (pattern : Twelve) (guard : d2746 pattern = 1) : d202 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16354 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16356 (pattern : Twelve) (guard : d2746 pattern = 1) : d1769 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16353 pattern childGuard
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16355 pattern childGuard
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16357 (pattern : Twelve) (guard : d2746 pattern = 1) : d1774 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16350 pattern childGuard
    simpa only [d1774, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16356 pattern childGuard
    simpa only [d1774, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16358 (pattern : Twelve) (guard : d2746 pattern = 1) : d1776 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16357 pattern childGuard
    simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16341 pattern childGuard
    simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16359 (pattern : Twelve) (guard : d2746 pattern = 1) : d1778 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16346 pattern childGuard
    simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16358 pattern childGuard
    simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16360 (pattern : Twelve) (guard : d2746 pattern = 1) : d1779 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16343 pattern childGuard
    simpa only [d1779, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16359 pattern childGuard
    simpa only [d1779, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16361 (pattern : Twelve) (guard : d2746 pattern = 1) : d26 pattern ≤ (1 : Int) + d26 pattern := by
  omega
theorem c16362 (pattern : Twelve) (guard : d0 pattern = 1) : d7 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16363 (pattern : Twelve) (guard : d2746 pattern = 1) : d17 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15934 pattern childGuard
    simpa only [d2746, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16362 pattern childGuard
    simpa only [d2746, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16364 (pattern : Twelve) (guard : d2746 pattern = 1) : d1 pattern ≤ (1 : Int) + d1 pattern := by
  omega
theorem c16365 (pattern : Twelve) (guard : d2746 pattern = 1) : d27 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d27, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16363 pattern childGuard
    simpa only [d27, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d27, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16364 pattern childGuard
    simpa only [d27, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16366 (pattern : Twelve) (guard : d2746 pattern = 1) : d50 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16361 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16365 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16367 (pattern : Twelve) (guard : d2746 pattern = 1) : d72 pattern ≤ (1 : Int) + d2593 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d72, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15933 pattern childGuard
    simpa only [d72, d2593, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d72, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16366 pattern childGuard
    simpa only [d72, d2593, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16368 (pattern : Twelve) (guard : d0 pattern = 1) : d9 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16369 (pattern : Twelve) (guard : d2746 pattern = 1) : d18 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15954 pattern childGuard
    simpa only [d2746, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16368 pattern childGuard
    simpa only [d2746, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16370 (pattern : Twelve) (guard : d2746 pattern = 1) : d28 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d28, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16363 pattern childGuard
    simpa only [d28, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d28, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16369 pattern childGuard
    simpa only [d28, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16371 (pattern : Twelve) (guard : d7 pattern = 1) : d10 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16137 pattern childGuard
    simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12013 pattern childGuard
    simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16372 (pattern : Twelve) (guard : d0 pattern = 1) : d11 pattern ≤ (1 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16373 (pattern : Twelve) (guard : d2746 pattern = 1) : d19 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16371 pattern childGuard
    simpa only [d2746, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16372 pattern childGuard
    simpa only [d2746, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16374 (pattern : Twelve) (guard : d2746 pattern = 1) : d29 pattern ≤ (1 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d29, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16373 pattern childGuard
    simpa only [d29, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d29, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d29, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16375 (pattern : Twelve) (guard : d2746 pattern = 1) : d51 pattern ≤ (1 : Int) + d65 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d51, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16370 pattern childGuard
    simpa only [d51, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d51, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16374 pattern childGuard
    simpa only [d51, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16376 (pattern : Twelve) (guard : d2746 pattern = 1) : d73 pattern ≤ (1 : Int) + d2896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d73, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15933 pattern childGuard
    simpa only [d73, d2896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d73, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16375 pattern childGuard
    simpa only [d73, d2896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16377 (pattern : Twelve) (guard : d2746 pattern = 1) : d91 pattern ≤ (1 : Int) + d2897 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d91, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16367 pattern childGuard
    simpa only [d91, d2897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d91, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16376 pattern childGuard
    simpa only [d91, d2897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16378 (pattern : Twelve) (guard : d2746 pattern = 1) : d30 pattern ≤ (1 : Int) + d30 pattern := by
  omega
theorem c16379 (pattern : Twelve) (guard : d7 pattern = 1) : d12 pattern ≤ (1 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16225 pattern childGuard
    simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11195 pattern childGuard
    simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
