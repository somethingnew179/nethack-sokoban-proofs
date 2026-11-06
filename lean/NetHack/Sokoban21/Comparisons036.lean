/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons035
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c5040 (pattern : Twelve) (guard : d1849 pattern = 1) : d399 pattern ≤ (0 : Int) + d268 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d399, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5039 pattern childGuard
    simpa only [d399, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d399, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5007 pattern childGuard
    simpa only [d399, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5041 (pattern : Twelve) (guard : d1849 pattern = 1) : d407 pattern ≤ (0 : Int) + d278 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d407, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5040 pattern childGuard
    simpa only [d407, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d407, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5010 pattern childGuard
    simpa only [d407, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5042 (pattern : Twelve) (guard : d1849 pattern = 1) : d412 pattern ≤ (0 : Int) + d287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d412, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5041 pattern childGuard
    simpa only [d412, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d412, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d412, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5043 (pattern : Twelve) (guard : d1849 pattern = 1) : d416 pattern ≤ (0 : Int) + d294 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d416, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5038 pattern childGuard
    simpa only [d416, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d416, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5042 pattern childGuard
    simpa only [d416, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5044 (pattern : Twelve) (guard : d1849 pattern = 1) : d419 pattern ≤ (0 : Int) + d297 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d419, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5013 pattern childGuard
    simpa only [d419, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d419, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5043 pattern childGuard
    simpa only [d419, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5045 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c881 pattern childGuard
    simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5046 (pattern : Twelve) (guard : d1849 pattern = 1) : d35 pattern ≤ (0 : Int) + d253 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c120 pattern childGuard
    simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5047 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5048 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d1848, d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5049 (pattern : Twelve) (guard : d1849 pattern = 1) : d380 pattern ≤ (0 : Int) + d254 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d380, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5048 pattern childGuard
    simpa only [d1849, d380, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d380, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c117 pattern childGuard
    simpa only [d1849, d380, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5050 (pattern : Twelve) (guard : d1849 pattern = 1) : d399 pattern ≤ (0 : Int) + d269 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d399, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5046 pattern childGuard
    simpa only [d399, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d399, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5049 pattern childGuard
    simpa only [d399, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5051 (pattern : Twelve) (guard : d1849 pattern = 1) : d407 pattern ≤ (0 : Int) + d279 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d407, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5050 pattern childGuard
    simpa only [d407, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d407, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5010 pattern childGuard
    simpa only [d407, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5052 (pattern : Twelve) (guard : d1849 pattern = 1) : d399 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5009 pattern childGuard
    simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5007 pattern childGuard
    simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5053 (pattern : Twelve) (guard : d1849 pattern = 1) : d407 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d407, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5052 pattern childGuard
    simpa only [d407, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d407, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5010 pattern childGuard
    simpa only [d407, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5054 (pattern : Twelve) (guard : d1849 pattern = 1) : d407 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5051 pattern childGuard
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5053 pattern childGuard
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5055 (pattern : Twelve) (guard : d1849 pattern = 1) : d397 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5032 pattern childGuard
    simpa only [d397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5030 pattern childGuard
    simpa only [d397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5056 (pattern : Twelve) (guard : d1849 pattern = 1) : d406 pattern ≤ (0 : Int) + d281 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d406, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5055 pattern childGuard
    simpa only [d406, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d406, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5036 pattern childGuard
    simpa only [d406, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5057 (pattern : Twelve) (guard : d1849 pattern = 1) : d413 pattern ≤ (0 : Int) + d289 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d413, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5053 pattern childGuard
    simpa only [d413, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d413, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5056 pattern childGuard
    simpa only [d413, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5058 (pattern : Twelve) (guard : d1849 pattern = 1) : d412 pattern ≤ (0 : Int) + d290 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d412, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5053 pattern childGuard
    simpa only [d412, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d412, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d412, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5059 (pattern : Twelve) (guard : d1849 pattern = 1) : d417 pattern ≤ (0 : Int) + d295 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d417, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5057 pattern childGuard
    simpa only [d417, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d417, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5058 pattern childGuard
    simpa only [d417, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5060 (pattern : Twelve) (guard : d1849 pattern = 1) : d420 pattern ≤ (0 : Int) + d298 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d420, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5054 pattern childGuard
    simpa only [d420, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d420, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5059 pattern childGuard
    simpa only [d420, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5061 (pattern : Twelve) (guard : d1849 pattern = 1) : d422 pattern ≤ (0 : Int) + d300 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d422, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5044 pattern childGuard
    simpa only [d422, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d422, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5060 pattern childGuard
    simpa only [d422, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5062 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d18 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5063 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d28 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d36, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5062 pattern childGuard
    simpa only [d1848, d36, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5064 (pattern : Twelve) (guard : d1849 pattern = 1) : d378 pattern ≤ (0 : Int) + d255 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d378, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5063 pattern childGuard
    simpa only [d1849, d378, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d378, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c101 pattern childGuard
    simpa only [d1849, d378, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5065 (pattern : Twelve) (guard : d1849 pattern = 1) : d394 pattern ≤ (0 : Int) + d270 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d394, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5046 pattern childGuard
    simpa only [d394, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d394, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5064 pattern childGuard
    simpa only [d394, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5066 (pattern : Twelve) (guard : d1849 pattern = 1) : d407 pattern ≤ (0 : Int) + d282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d407, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5050 pattern childGuard
    simpa only [d407, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d407, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5065 pattern childGuard
    simpa only [d407, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5067 (pattern : Twelve) (guard : d1849 pattern = 1) : d407 pattern ≤ (0 : Int) + d291 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5066 pattern childGuard
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5053 pattern childGuard
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5068 (pattern : Twelve) (guard : d1849 pattern = 1) : d394 pattern ≤ (0 : Int) + d271 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d394, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5046 pattern childGuard
    simpa only [d394, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d394, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4986 pattern childGuard
    simpa only [d394, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5069 (pattern : Twelve) (guard : d1849 pattern = 1) : d407 pattern ≤ (0 : Int) + d283 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d407, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5050 pattern childGuard
    simpa only [d407, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d407, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5068 pattern childGuard
    simpa only [d407, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5070 (pattern : Twelve) (guard : d1849 pattern = 1) : d407 pattern ≤ (0 : Int) + d292 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5069 pattern childGuard
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5053 pattern childGuard
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5071 (pattern : Twelve) (guard : d1849 pattern = 1) : d407 pattern ≤ (0 : Int) + d296 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5067 pattern childGuard
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5070 pattern childGuard
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5072 (pattern : Twelve) (guard : d1849 pattern = 1) : d420 pattern ≤ (0 : Int) + d299 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d420, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5071 pattern childGuard
    simpa only [d420, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d420, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5059 pattern childGuard
    simpa only [d420, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5073 (pattern : Twelve) (guard : d1849 pattern = 1) : d420 pattern ≤ (0 : Int) + d301 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5072 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5060 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5074 (pattern : Twelve) (guard : d1849 pattern = 1) : d423 pattern ≤ (0 : Int) + d302 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d423, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5061 pattern childGuard
    simpa only [d423, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d423, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5073 pattern childGuard
    simpa only [d423, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5075 (pattern : Twelve) (guard : d1849 pattern = 1) : d386 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d386, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5028 pattern childGuard
    simpa only [d1849, d386, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d386, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c353 pattern childGuard
    simpa only [d1849, d386, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5076 (pattern : Twelve) (guard : d1849 pattern = 1) : d400 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5032 pattern childGuard
    simpa only [d400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5075 pattern childGuard
    simpa only [d400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5077 (pattern : Twelve) (guard : d1849 pattern = 1) : d387 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d387, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5028 pattern childGuard
    simpa only [d1849, d387, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d387, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c192 pattern childGuard
    simpa only [d1849, d387, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5078 (pattern : Twelve) (guard : d1849 pattern = 1) : d388 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d388, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5034 pattern childGuard
    simpa only [d1849, d388, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d388, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c411 pattern childGuard
    simpa only [d1849, d388, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5079 (pattern : Twelve) (guard : d1849 pattern = 1) : d401 pattern ≤ (0 : Int) + d267 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d401, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5077 pattern childGuard
    simpa only [d401, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d401, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5078 pattern childGuard
    simpa only [d401, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5080 (pattern : Twelve) (guard : d1849 pattern = 1) : d408 pattern ≤ (0 : Int) + d281 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d408, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5076 pattern childGuard
    simpa only [d408, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d408, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5079 pattern childGuard
    simpa only [d408, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5081 (pattern : Twelve) (guard : d1849 pattern = 1) : d414 pattern ≤ (0 : Int) + d289 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d414, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5053 pattern childGuard
    simpa only [d414, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d414, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5080 pattern childGuard
    simpa only [d414, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5082 (pattern : Twelve) (guard : d1849 pattern = 1) : d418 pattern ≤ (0 : Int) + d295 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d418, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5081 pattern childGuard
    simpa only [d418, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d418, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5058 pattern childGuard
    simpa only [d418, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5083 (pattern : Twelve) (guard : d1849 pattern = 1) : d421 pattern ≤ (0 : Int) + d299 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d421, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5071 pattern childGuard
    simpa only [d421, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d421, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5082 pattern childGuard
    simpa only [d421, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5084 (pattern : Twelve) (guard : d1849 pattern = 1) : d421 pattern ≤ (0 : Int) + d298 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d421, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5054 pattern childGuard
    simpa only [d421, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d421, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5082 pattern childGuard
    simpa only [d421, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5085 (pattern : Twelve) (guard : d1849 pattern = 1) : d421 pattern ≤ (0 : Int) + d301 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5083 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5084 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5086 (pattern : Twelve) (guard : d1849 pattern = 1) : d424 pattern ≤ (0 : Int) + d303 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d424, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5074 pattern childGuard
    simpa only [d424, d303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d424, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5085 pattern childGuard
    simpa only [d424, d303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5087 (pattern : Twelve) (guard : d0 pattern = 1) : d163 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5088 (pattern : Twelve) (guard : d1848 pattern = 1) : d366 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d366, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d366, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d366, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5087 pattern childGuard
    simpa only [d1848, d366, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5089 (pattern : Twelve) (guard : d0 pattern = 1) : d818 pattern ≤ (0 : Int) + d173 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5090 (pattern : Twelve) (guard : d1849 pattern = 1) : d1030 pattern ≤ (0 : Int) + d940 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1030, d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5088 pattern childGuard
    simpa only [d1849, d1030, d940, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1030, d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5089 pattern childGuard
    simpa only [d1849, d1030, d940, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5091 (pattern : Twelve) (guard : d1849 pattern = 1) : d1038 pattern ≤ (0 : Int) + d947 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1038, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4968 pattern childGuard
    simpa only [d1038, d947, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1038, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5090 pattern childGuard
    simpa only [d1038, d947, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5092 (pattern : Twelve) (guard : d0 pattern = 1) : d163 pattern ≤ (0 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5093 (pattern : Twelve) (guard : d1848 pattern = 1) : d366 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d366, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5092 pattern childGuard
    simpa only [d1848, d366, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5094 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d173 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5095 (pattern : Twelve) (guard : d1849 pattern = 1) : d1031 pattern ≤ (0 : Int) + d941 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1031, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5093 pattern childGuard
    simpa only [d1849, d1031, d941, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1031, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5094 pattern childGuard
    simpa only [d1849, d1031, d941, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5096 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (0 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d29, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1105 pattern childGuard
    simpa only [d1848, d29, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5097 (pattern : Twelve) (guard : d1849 pattern = 1) : d1032 pattern ≤ (0 : Int) + d942 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1032, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5096 pattern childGuard
    simpa only [d1849, d1032, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1032, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c144 pattern childGuard
    simpa only [d1849, d1032, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5098 (pattern : Twelve) (guard : d1849 pattern = 1) : d1039 pattern ≤ (0 : Int) + d948 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1039, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5095 pattern childGuard
    simpa only [d1039, d948, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1039, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5097 pattern childGuard
    simpa only [d1039, d948, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5099 (pattern : Twelve) (guard : d1849 pattern = 1) : d1048 pattern ≤ (0 : Int) + d955 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1048, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5091 pattern childGuard
    simpa only [d1048, d955, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1048, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5098 pattern childGuard
    simpa only [d1048, d955, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5100 (pattern : Twelve) (guard : d1849 pattern = 1) : d1033 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1033, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d1849, d1033, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1033, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c249 pattern childGuard
    simpa only [d1849, d1033, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5101 (pattern : Twelve) (guard : d1849 pattern = 1) : d1040 pattern ≤ (0 : Int) + d259 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1040, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4983 pattern childGuard
    simpa only [d1040, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1040, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5100 pattern childGuard
    simpa only [d1040, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5102 (pattern : Twelve) (guard : d1849 pattern = 1) : d36 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c117 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5103 (pattern : Twelve) (guard : d1849 pattern = 1) : d1041 pattern ≤ (0 : Int) + d949 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1041, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5102 pattern childGuard
    simpa only [d1041, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1041, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5097 pattern childGuard
    simpa only [d1041, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5104 (pattern : Twelve) (guard : d1849 pattern = 1) : d1049 pattern ≤ (0 : Int) + d956 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1049, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5101 pattern childGuard
    simpa only [d1049, d956, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1049, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5103 pattern childGuard
    simpa only [d1049, d956, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5105 (pattern : Twelve) (guard : d1849 pattern = 1) : d1054 pattern ≤ (0 : Int) + d963 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1054, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5099 pattern childGuard
    simpa only [d1054, d963, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1054, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5104 pattern childGuard
    simpa only [d1054, d963, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5106 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d1848, d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5107 (pattern : Twelve) (guard : d1849 pattern = 1) : d1033 pattern ≤ (0 : Int) + d943 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1033, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5106 pattern childGuard
    simpa only [d1849, d1033, d943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1033, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c249 pattern childGuard
    simpa only [d1849, d1033, d943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5108 (pattern : Twelve) (guard : d1849 pattern = 1) : d1040 pattern ≤ (0 : Int) + d950 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1040, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4999 pattern childGuard
    simpa only [d1040, d950, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1040, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5107 pattern childGuard
    simpa only [d1040, d950, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5109 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c980 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5110 (pattern : Twelve) (guard : d1849 pattern = 1) : d36 pattern ≤ (0 : Int) + d944 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5109 pattern childGuard
    simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c117 pattern childGuard
    simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5111 (pattern : Twelve) (guard : d1849 pattern = 1) : d1041 pattern ≤ (0 : Int) + d951 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1041, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5110 pattern childGuard
    simpa only [d1041, d951, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1041, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5097 pattern childGuard
    simpa only [d1041, d951, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5112 (pattern : Twelve) (guard : d1849 pattern = 1) : d1049 pattern ≤ (0 : Int) + d957 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1049, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5108 pattern childGuard
    simpa only [d1049, d957, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1049, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5111 pattern childGuard
    simpa only [d1049, d957, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5113 (pattern : Twelve) (guard : d1849 pattern = 1) : d1042 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1042, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5009 pattern childGuard
    simpa only [d1042, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1042, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5100 pattern childGuard
    simpa only [d1042, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5114 (pattern : Twelve) (guard : d1849 pattern = 1) : d1050 pattern ≤ (0 : Int) + d958 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1050, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5113 pattern childGuard
    simpa only [d1050, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1050, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5103 pattern childGuard
    simpa only [d1050, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5115 (pattern : Twelve) (guard : d1849 pattern = 1) : d1055 pattern ≤ (0 : Int) + d964 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1055, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5112 pattern childGuard
    simpa only [d1055, d964, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1055, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5114 pattern childGuard
    simpa only [d1055, d964, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5116 (pattern : Twelve) (guard : d1849 pattern = 1) : d1060 pattern ≤ (0 : Int) + d970 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1060, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5105 pattern childGuard
    simpa only [d1060, d970, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1060, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5115 pattern childGuard
    simpa only [d1060, d970, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5117 (pattern : Twelve) (guard : d1849 pattern = 1) : d1043 pattern ≤ (0 : Int) + d265 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1043, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5024 pattern childGuard
    simpa only [d1043, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1043, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5100 pattern childGuard
    simpa only [d1043, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5118 (pattern : Twelve) (guard : d1849 pattern = 1) : d1051 pattern ≤ (0 : Int) + d959 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1051, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5117 pattern childGuard
    simpa only [d1051, d959, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1051, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5103 pattern childGuard
    simpa only [d1051, d959, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5119 (pattern : Twelve) (guard : d1849 pattern = 1) : d1034 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1034, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5034 pattern childGuard
    simpa only [d1849, d1034, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1034, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c274 pattern childGuard
    simpa only [d1849, d1034, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5120 (pattern : Twelve) (guard : d1849 pattern = 1) : d1044 pattern ≤ (0 : Int) + d267 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1044, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5032 pattern childGuard
    simpa only [d1044, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1044, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5119 pattern childGuard
    simpa only [d1044, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5121 (pattern : Twelve) (guard : d1849 pattern = 1) : d40 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5034 pattern childGuard
    simpa only [d1849, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c138 pattern childGuard
    simpa only [d1849, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5122 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d21 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5123 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (0 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d42, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c392 pattern childGuard
    simpa only [d1848, d42, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d42, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5122 pattern childGuard
    simpa only [d1848, d42, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5124 (pattern : Twelve) (guard : d1849 pattern = 1) : d1035 pattern ≤ (0 : Int) + d945 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1035, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5123 pattern childGuard
    simpa only [d1849, d1035, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1035, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c279 pattern childGuard
    simpa only [d1849, d1035, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5125 (pattern : Twelve) (guard : d1849 pattern = 1) : d1045 pattern ≤ (0 : Int) + d952 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1045, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5121 pattern childGuard
    simpa only [d1045, d952, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1045, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5124 pattern childGuard
    simpa only [d1045, d952, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5126 (pattern : Twelve) (guard : d1849 pattern = 1) : d1052 pattern ≤ (0 : Int) + d960 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1052, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5120 pattern childGuard
    simpa only [d1052, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1052, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5125 pattern childGuard
    simpa only [d1052, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5127 (pattern : Twelve) (guard : d1849 pattern = 1) : d1056 pattern ≤ (0 : Int) + d965 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1056, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5118 pattern childGuard
    simpa only [d1056, d965, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1056, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5126 pattern childGuard
    simpa only [d1056, d965, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5128 (pattern : Twelve) (guard : d1849 pattern = 1) : d1057 pattern ≤ (0 : Int) + d966 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1057, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5114 pattern childGuard
    simpa only [d1057, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1057, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1057, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5129 (pattern : Twelve) (guard : d1849 pattern = 1) : d1061 pattern ≤ (0 : Int) + d971 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1061, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5127 pattern childGuard
    simpa only [d1061, d971, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1061, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5128 pattern childGuard
    simpa only [d1061, d971, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5130 (pattern : Twelve) (guard : d1849 pattern = 1) : d1064 pattern ≤ (0 : Int) + d973 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1064, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5116 pattern childGuard
    simpa only [d1064, d973, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1064, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5129 pattern childGuard
    simpa only [d1064, d973, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5131 (pattern : Twelve) (guard : d1849 pattern = 1) : d1042 pattern ≤ (0 : Int) + d953 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1042, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5046 pattern childGuard
    simpa only [d1042, d953, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1042, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5107 pattern childGuard
    simpa only [d1042, d953, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5132 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d36, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5005 pattern childGuard
    simpa only [d1848, d36, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5133 (pattern : Twelve) (guard : d1849 pattern = 1) : d36 pattern ≤ (0 : Int) + d946 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5132 pattern childGuard
    simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c117 pattern childGuard
    simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5134 (pattern : Twelve) (guard : d1849 pattern = 1) : d1041 pattern ≤ (0 : Int) + d954 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1041, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5133 pattern childGuard
    simpa only [d1041, d954, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1041, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5097 pattern childGuard
    simpa only [d1041, d954, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5135 (pattern : Twelve) (guard : d1849 pattern = 1) : d1050 pattern ≤ (0 : Int) + d961 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1050, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5131 pattern childGuard
    simpa only [d1050, d961, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1050, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5134 pattern childGuard
    simpa only [d1050, d961, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5136 (pattern : Twelve) (guard : d1849 pattern = 1) : d1050 pattern ≤ (0 : Int) + d967 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5135 pattern childGuard
    simpa only [d967, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5114 pattern childGuard
    simpa only [d967, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5137 (pattern : Twelve) (guard : d1849 pattern = 1) : d1058 pattern ≤ (0 : Int) + d968 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1058, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5114 pattern childGuard
    simpa only [d1058, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1058, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5126 pattern childGuard
    simpa only [d1058, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5138 (pattern : Twelve) (guard : d1849 pattern = 1) : d1062 pattern ≤ (0 : Int) + d972 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1062, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5137 pattern childGuard
    simpa only [d1062, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1062, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5128 pattern childGuard
    simpa only [d1062, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5139 (pattern : Twelve) (guard : d1849 pattern = 1) : d1065 pattern ≤ (0 : Int) + d974 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1065, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5136 pattern childGuard
    simpa only [d1065, d974, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1065, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5138 pattern childGuard
    simpa only [d1065, d974, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5140 (pattern : Twelve) (guard : d1849 pattern = 1) : d1067 pattern ≤ (0 : Int) + d976 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1067, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5130 pattern childGuard
    simpa only [d1067, d976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1067, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5139 pattern childGuard
    simpa only [d1067, d976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5141 (pattern : Twelve) (guard : d1849 pattern = 1) : d1050 pattern ≤ (0 : Int) + d962 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1050, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5131 pattern childGuard
    simpa only [d1050, d962, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1050, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5111 pattern childGuard
    simpa only [d1050, d962, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5142 (pattern : Twelve) (guard : d1849 pattern = 1) : d1050 pattern ≤ (0 : Int) + d969 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5141 pattern childGuard
    simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5114 pattern childGuard
    simpa only [d969, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5143 (pattern : Twelve) (guard : d1849 pattern = 1) : d1065 pattern ≤ (0 : Int) + d975 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1065, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5142 pattern childGuard
    simpa only [d1065, d975, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1065, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5138 pattern childGuard
    simpa only [d1065, d975, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5144 (pattern : Twelve) (guard : d1849 pattern = 1) : d1065 pattern ≤ (0 : Int) + d977 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5143 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5139 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5145 (pattern : Twelve) (guard : d1849 pattern = 1) : d1068 pattern ≤ (0 : Int) + d978 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1068, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5140 pattern childGuard
    simpa only [d1068, d978, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1068, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5144 pattern childGuard
    simpa only [d1068, d978, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5146 (pattern : Twelve) (guard : d0 pattern = 1) : d880 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5147 (pattern : Twelve) (guard : d1849 pattern = 1) : d1036 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1036, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5034 pattern childGuard
    simpa only [d1849, d1036, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1036, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5146 pattern childGuard
    simpa only [d1849, d1036, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5148 (pattern : Twelve) (guard : d1849 pattern = 1) : d1046 pattern ≤ (0 : Int) + d267 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1046, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5032 pattern childGuard
    simpa only [d1046, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1046, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5147 pattern childGuard
    simpa only [d1046, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5149 (pattern : Twelve) (guard : d1849 pattern = 1) : d1037 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1037, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5034 pattern childGuard
    simpa only [d1849, d1037, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1037, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c353 pattern childGuard
    simpa only [d1849, d1037, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5150 (pattern : Twelve) (guard : d1849 pattern = 1) : d889 pattern ≤ (0 : Int) + d945 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d889, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5123 pattern childGuard
    simpa only [d1849, d889, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d889, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1849, d889, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5151 (pattern : Twelve) (guard : d1849 pattern = 1) : d1047 pattern ≤ (0 : Int) + d952 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1047, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5149 pattern childGuard
    simpa only [d1047, d952, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1047, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5150 pattern childGuard
    simpa only [d1047, d952, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5152 (pattern : Twelve) (guard : d1849 pattern = 1) : d1053 pattern ≤ (0 : Int) + d960 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1053, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5148 pattern childGuard
    simpa only [d1053, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1053, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5151 pattern childGuard
    simpa only [d1053, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5153 (pattern : Twelve) (guard : d1849 pattern = 1) : d1059 pattern ≤ (0 : Int) + d968 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1059, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5114 pattern childGuard
    simpa only [d1059, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1059, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5152 pattern childGuard
    simpa only [d1059, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5154 (pattern : Twelve) (guard : d1849 pattern = 1) : d1063 pattern ≤ (0 : Int) + d972 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1063, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5153 pattern childGuard
    simpa only [d1063, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1063, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5128 pattern childGuard
    simpa only [d1063, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5155 (pattern : Twelve) (guard : d1849 pattern = 1) : d1066 pattern ≤ (0 : Int) + d975 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1066, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5142 pattern childGuard
    simpa only [d1066, d975, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1066, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5154 pattern childGuard
    simpa only [d1066, d975, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5156 (pattern : Twelve) (guard : d1849 pattern = 1) : d1066 pattern ≤ (0 : Int) + d974 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1066, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5136 pattern childGuard
    simpa only [d1066, d974, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1066, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5154 pattern childGuard
    simpa only [d1066, d974, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5157 (pattern : Twelve) (guard : d1849 pattern = 1) : d1066 pattern ≤ (0 : Int) + d977 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5155 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5156 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5158 (pattern : Twelve) (guard : d1849 pattern = 1) : d1069 pattern ≤ (0 : Int) + d979 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1069, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5145 pattern childGuard
    simpa only [d1069, d979, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1069, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5157 pattern childGuard
    simpa only [d1069, d979, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5159 (pattern : Twelve) (guard : d1848 pattern = 1) : d1444 pattern ≤ (0 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1444, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d1848, d1444, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1444, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1043 pattern childGuard
    simpa only [d1848, d1444, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5160 (pattern : Twelve) (guard : d1849 pattern = 1) : d1445 pattern ≤ (0 : Int) + d1380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1445, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5159 pattern childGuard
    simpa only [d1849, d1445, d1380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1445, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c334 pattern childGuard
    simpa only [d1849, d1445, d1380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5161 (pattern : Twelve) (guard : d1849 pattern = 1) : d1448 pattern ≤ (0 : Int) + d1385 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1448, d1385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5095 pattern childGuard
    simpa only [d1448, d1385, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1448, d1385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5160 pattern childGuard
    simpa only [d1448, d1385, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5162 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1046 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5163 (pattern : Twelve) (guard : d1849 pattern = 1) : d29 pattern ≤ (0 : Int) + d1381 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5162 pattern childGuard
    simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c101 pattern childGuard
    simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5164 (pattern : Twelve) (guard : d1849 pattern = 1) : d1449 pattern ≤ (0 : Int) + d1386 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1449, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5163 pattern childGuard
    simpa only [d1449, d1386, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1449, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1449, d1386, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5165 (pattern : Twelve) (guard : d1849 pattern = 1) : d1455 pattern ≤ (0 : Int) + d1393 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1455, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5161 pattern childGuard
    simpa only [d1455, d1393, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1455, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5164 pattern childGuard
    simpa only [d1455, d1393, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5166 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1276 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5167 (pattern : Twelve) (guard : d1848 pattern = 1) : d1444 pattern ≤ (0 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1444, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d1848, d1444, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1444, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5166 pattern childGuard
    simpa only [d1848, d1444, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5168 (pattern : Twelve) (guard : d1849 pattern = 1) : d1445 pattern ≤ (0 : Int) + d1382 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1445, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5167 pattern childGuard
    simpa only [d1849, d1445, d1382, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1445, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c334 pattern childGuard
    simpa only [d1849, d1445, d1382, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5169 (pattern : Twelve) (guard : d1849 pattern = 1) : d1450 pattern ≤ (0 : Int) + d1387 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1450, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5102 pattern childGuard
    simpa only [d1450, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1450, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5168 pattern childGuard
    simpa only [d1450, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5170 (pattern : Twelve) (guard : d1849 pattern = 1) : d29 pattern ≤ (0 : Int) + d942 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5096 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c101 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5171 (pattern : Twelve) (guard : d1849 pattern = 1) : d1449 pattern ≤ (0 : Int) + d1388 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1449, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5170 pattern childGuard
    simpa only [d1449, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1449, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d1449, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5172 (pattern : Twelve) (guard : d1849 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1394 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1456, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5169 pattern childGuard
    simpa only [d1456, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1456, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5171 pattern childGuard
    simpa only [d1456, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5173 (pattern : Twelve) (guard : d1849 pattern = 1) : d1459 pattern ≤ (0 : Int) + d1398 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1459, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5165 pattern childGuard
    simpa only [d1459, d1398, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1459, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5172 pattern childGuard
    simpa only [d1459, d1398, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5174 (pattern : Twelve) (guard : d1849 pattern = 1) : d1450 pattern ≤ (0 : Int) + d1389 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1450, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5110 pattern childGuard
    simpa only [d1450, d1389, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1450, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5160 pattern childGuard
    simpa only [d1450, d1389, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5175 (pattern : Twelve) (guard : d1849 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1395 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1456, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5174 pattern childGuard
    simpa only [d1456, d1395, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1456, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5164 pattern childGuard
    simpa only [d1456, d1395, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5176 (pattern : Twelve) (guard : d1849 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1399 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5175 pattern childGuard
    simpa only [d1399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5172 pattern childGuard
    simpa only [d1399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5177 (pattern : Twelve) (guard : d1849 pattern = 1) : d1463 pattern ≤ (0 : Int) + d1403 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1463, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5173 pattern childGuard
    simpa only [d1463, d1403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1463, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5176 pattern childGuard
    simpa only [d1463, d1403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5178 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1277 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5179 (pattern : Twelve) (guard : d1848 pattern = 1) : d1330 pattern ≤ (0 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1330, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1489 pattern childGuard
    simpa only [d1848, d1330, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1330, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5178 pattern childGuard
    simpa only [d1848, d1330, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
