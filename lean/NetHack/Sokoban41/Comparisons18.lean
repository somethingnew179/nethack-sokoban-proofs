/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons17
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c2880 (pattern : Ten) (guard : d460 pattern = 1) : d267 pattern ≤ (2 : Int) + d473 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d267, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2877 pattern childGuard
    simpa only [d267, d473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d267, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2879 pattern childGuard
    simpa only [d267, d473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2881 (pattern : Ten) (guard : d460 pattern = 1) : d10 pattern ≤ (2 : Int) + d10 pattern := by
  omega
theorem c2882 (pattern : Ten) (guard : d460 pattern = 1) : d268 pattern ≤ (2 : Int) + d254 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d268, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2879 pattern childGuard
    simpa only [d268, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d268, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2881 pattern childGuard
    simpa only [d268, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2883 (pattern : Ten) (guard : d460 pattern = 1) : d271 pattern ≤ (2 : Int) + d474 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d271, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2880 pattern childGuard
    simpa only [d271, d474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d271, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2882 pattern childGuard
    simpa only [d271, d474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2884 (pattern : Ten) (guard : d0 pattern = 1) : d174 pattern ≤ (2 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2885 (pattern : Ten) (guard : d460 pattern = 1) : d174 pattern ≤ (2 : Int) + d251 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d385 pattern = 1 := by simpa only [d460, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2876 pattern childGuard
    simpa only [d460, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d460, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2884 pattern childGuard
    simpa only [d460, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2886 (pattern : Ten) (guard : d0 pattern = 1) : d172 pattern ≤ (2 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2887 (pattern : Ten) (guard : d385 pattern = 1) : d199 pattern ≤ (2 : Int) + d172 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d385, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2886 pattern childGuard
    simpa only [d385, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d385, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2414 pattern childGuard
    simpa only [d385, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2888 (pattern : Ten) (guard : d0 pattern = 1) : d199 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2889 (pattern : Ten) (guard : d460 pattern = 1) : d199 pattern ≤ (2 : Int) + d252 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d385 pattern = 1 := by simpa only [d460, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2887 pattern childGuard
    simpa only [d460, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d460, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2888 pattern childGuard
    simpa only [d460, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2890 (pattern : Ten) (guard : d460 pattern = 1) : d269 pattern ≤ (2 : Int) + d255 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d269, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2885 pattern childGuard
    simpa only [d269, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d269, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2889 pattern childGuard
    simpa only [d269, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2891 (pattern : Ten) (guard : d460 pattern = 1) : d272 pattern ≤ (2 : Int) + d258 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d272, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2890 pattern childGuard
    simpa only [d272, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d272, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2882 pattern childGuard
    simpa only [d272, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2892 (pattern : Ten) (guard : d460 pattern = 1) : d275 pattern ≤ (2 : Int) + d475 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d275, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2883 pattern childGuard
    simpa only [d275, d475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d275, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2891 pattern childGuard
    simpa only [d275, d475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2893 (pattern : Ten) (guard : d460 pattern = 1) : d273 pattern ≤ (2 : Int) + d259 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d273, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2882 pattern childGuard
    simpa only [d273, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d273, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2881 pattern childGuard
    simpa only [d273, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2894 (pattern : Ten) (guard : d460 pattern = 1) : d270 pattern ≤ (2 : Int) + d256 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d270, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2889 pattern childGuard
    simpa only [d270, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d270, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2881 pattern childGuard
    simpa only [d270, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2895 (pattern : Ten) (guard : d460 pattern = 1) : d274 pattern ≤ (2 : Int) + d260 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d274, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2894 pattern childGuard
    simpa only [d274, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d274, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2881 pattern childGuard
    simpa only [d274, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2896 (pattern : Ten) (guard : d460 pattern = 1) : d276 pattern ≤ (2 : Int) + d262 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d276, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2893 pattern childGuard
    simpa only [d276, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d276, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2895 pattern childGuard
    simpa only [d276, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2897 (pattern : Ten) (guard : d460 pattern = 1) : d277 pattern ≤ (2 : Int) + d476 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d277, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2892 pattern childGuard
    simpa only [d277, d476, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d277, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2896 pattern childGuard
    simpa only [d277, d476, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2898 (pattern : Ten) (guard : d460 pattern = 1) : d278 pattern ≤ (2 : Int) + d264 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d278, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2896 pattern childGuard
    simpa only [d278, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d278, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2881 pattern childGuard
    simpa only [d278, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2899 (pattern : Ten) (guard : d460 pattern = 1) : d279 pattern ≤ (2 : Int) + d477 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d279, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2897 pattern childGuard
    simpa only [d279, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d279, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2898 pattern childGuard
    simpa only [d279, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2900 (pattern : Ten) (guard : d0 pattern = 1) : d86 pattern ≤ (0 : Int) + d15 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2901 (pattern : Ten) (guard : d479 pattern = 1) : d87 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d479, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2900 pattern childGuard
    simpa only [d479, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d479, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c504 pattern childGuard
    simpa only [d479, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2902 (pattern : Ten) (guard : d0 pattern = 1) : d88 pattern ≤ (0 : Int) + d15 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2903 (pattern : Ten) (guard : d480 pattern = 1) : d93 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d479 pattern = 1 := by simpa only [d480, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2901 pattern childGuard
    simpa only [d480, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d480, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2902 pattern childGuard
    simpa only [d480, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2904 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d14 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2905 (pattern : Ten) (guard : d479 pattern = 1) : d89 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d479, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2904 pattern childGuard
    simpa only [d479, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d479, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c510 pattern childGuard
    simpa only [d479, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2906 (pattern : Ten) (guard : d0 pattern = 1) : d90 pattern ≤ (0 : Int) + d14 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2907 (pattern : Ten) (guard : d480 pattern = 1) : d94 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d479 pattern = 1 := by simpa only [d480, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2905 pattern childGuard
    simpa only [d480, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d480, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2906 pattern childGuard
    simpa only [d480, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2908 (pattern : Ten) (guard : d480 pattern = 1) : d99 pattern ≤ (0 : Int) + d481 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d99, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2903 pattern childGuard
    simpa only [d99, d481, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d99, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2907 pattern childGuard
    simpa only [d99, d481, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2909 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d44 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2910 (pattern : Ten) (guard : d479 pattern = 1) : d91 pattern ≤ (0 : Int) + d44 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d479, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2909 pattern childGuard
    simpa only [d479, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d479, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c518 pattern childGuard
    simpa only [d479, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2911 (pattern : Ten) (guard : d0 pattern = 1) : d92 pattern ≤ (0 : Int) + d44 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2912 (pattern : Ten) (guard : d480 pattern = 1) : d95 pattern ≤ (0 : Int) + d44 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d479 pattern = 1 := by simpa only [d480, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2910 pattern childGuard
    simpa only [d480, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d480, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2911 pattern childGuard
    simpa only [d480, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2913 (pattern : Ten) (guard : d480 pattern = 1) : d100 pattern ≤ (0 : Int) + d482 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d100, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2912 pattern childGuard
    simpa only [d100, d482, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d100, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2907 pattern childGuard
    simpa only [d100, d482, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2914 (pattern : Ten) (guard : d480 pattern = 1) : d103 pattern ≤ (0 : Int) + d483 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d103, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2908 pattern childGuard
    simpa only [d103, d483, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d103, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2913 pattern childGuard
    simpa only [d103, d483, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2915 (pattern : Ten) (guard : d479 pattern = 1) : d88 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d479, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c90 pattern childGuard
    simpa only [d479, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d479, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d479, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2916 (pattern : Ten) (guard : d480 pattern = 1) : d96 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d479 pattern = 1 := by simpa only [d480, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2915 pattern childGuard
    simpa only [d480, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d480, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d480, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2917 (pattern : Ten) (guard : d479 pattern = 1) : d90 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d479, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c462 pattern childGuard
    simpa only [d479, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d479, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d479, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2918 (pattern : Ten) (guard : d480 pattern = 1) : d97 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d479 pattern = 1 := by simpa only [d480, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2917 pattern childGuard
    simpa only [d480, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d480, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d480, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2919 (pattern : Ten) (guard : d480 pattern = 1) : d101 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2916 pattern childGuard
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2918 pattern childGuard
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2920 (pattern : Ten) (guard : d479 pattern = 1) : d92 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d479, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c469 pattern childGuard
    simpa only [d479, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d479, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d479, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2921 (pattern : Ten) (guard : d480 pattern = 1) : d98 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d479 pattern = 1 := by simpa only [d480, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2920 pattern childGuard
    simpa only [d480, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d480, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d480, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2922 (pattern : Ten) (guard : d480 pattern = 1) : d102 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2921 pattern childGuard
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2918 pattern childGuard
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2923 (pattern : Ten) (guard : d480 pattern = 1) : d104 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2919 pattern childGuard
    simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2924 (pattern : Ten) (guard : d480 pattern = 1) : d105 pattern ≤ (0 : Int) + d484 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d105, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2914 pattern childGuard
    simpa only [d105, d484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d105, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2923 pattern childGuard
    simpa only [d105, d484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2925 (pattern : Ten) (guard : d480 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c2926 (pattern : Ten) (guard : d480 pattern = 1) : d106 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2923 pattern childGuard
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2925 pattern childGuard
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2927 (pattern : Ten) (guard : d480 pattern = 1) : d107 pattern ≤ (0 : Int) + d485 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d107, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2924 pattern childGuard
    simpa only [d107, d485, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d107, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2926 pattern childGuard
    simpa only [d107, d485, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2928 (pattern : Ten) (guard : d0 pattern = 1) : d173 pattern ≤ (0 : Int) + d174 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2929 (pattern : Ten) (guard : d486 pattern = 1) : d249 pattern ≤ (0 : Int) + d174 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d486, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2928 pattern childGuard
    simpa only [d486, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d486, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c537 pattern childGuard
    simpa only [d486, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2930 (pattern : Ten) (guard : d0 pattern = 1) : d250 pattern ≤ (0 : Int) + d174 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2931 (pattern : Ten) (guard : d487 pattern = 1) : d253 pattern ≤ (0 : Int) + d174 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d486 pattern = 1 := by simpa only [d487, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2929 pattern childGuard
    simpa only [d487, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d487, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2930 pattern childGuard
    simpa only [d487, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2932 (pattern : Ten) (guard : d486 pattern = 1) : d250 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d486, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c429 pattern childGuard
    simpa only [d486, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d486, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d486, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2933 (pattern : Ten) (guard : d487 pattern = 1) : d254 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d486 pattern = 1 := by simpa only [d487, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2932 pattern childGuard
    simpa only [d487, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d487, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d487, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2934 (pattern : Ten) (guard : d487 pattern = 1) : d257 pattern ≤ (0 : Int) + d488 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d257, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2931 pattern childGuard
    simpa only [d257, d488, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d257, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d257, d488, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2935 (pattern : Ten) (guard : d0 pattern = 1) : d171 pattern ≤ (0 : Int) + d199 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2936 (pattern : Ten) (guard : d486 pattern = 1) : d251 pattern ≤ (0 : Int) + d199 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d486, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2935 pattern childGuard
    simpa only [d486, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d486, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c547 pattern childGuard
    simpa only [d486, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2937 (pattern : Ten) (guard : d0 pattern = 1) : d252 pattern ≤ (0 : Int) + d199 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2938 (pattern : Ten) (guard : d487 pattern = 1) : d255 pattern ≤ (0 : Int) + d199 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d486 pattern = 1 := by simpa only [d487, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2936 pattern childGuard
    simpa only [d487, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d487, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2937 pattern childGuard
    simpa only [d487, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2939 (pattern : Ten) (guard : d487 pattern = 1) : d258 pattern ≤ (0 : Int) + d489 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d258, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2938 pattern childGuard
    simpa only [d258, d489, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d258, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d258, d489, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2940 (pattern : Ten) (guard : d487 pattern = 1) : d261 pattern ≤ (0 : Int) + d490 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d261, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2934 pattern childGuard
    simpa only [d261, d490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d261, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2939 pattern childGuard
    simpa only [d261, d490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2941 (pattern : Ten) (guard : d487 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c2942 (pattern : Ten) (guard : d487 pattern = 1) : d259 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2941 pattern childGuard
    simpa only [d259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2943 (pattern : Ten) (guard : d486 pattern = 1) : d252 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d486, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c487 pattern childGuard
    simpa only [d486, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d486, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d486, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2944 (pattern : Ten) (guard : d487 pattern = 1) : d256 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d486 pattern = 1 := by simpa only [d487, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2943 pattern childGuard
    simpa only [d487, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d487, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d487, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2945 (pattern : Ten) (guard : d487 pattern = 1) : d260 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2944 pattern childGuard
    simpa only [d260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2941 pattern childGuard
    simpa only [d260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2946 (pattern : Ten) (guard : d487 pattern = 1) : d262 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2942 pattern childGuard
    simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2945 pattern childGuard
    simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2947 (pattern : Ten) (guard : d487 pattern = 1) : d263 pattern ≤ (0 : Int) + d491 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d263, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2940 pattern childGuard
    simpa only [d263, d491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d263, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2946 pattern childGuard
    simpa only [d263, d491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2948 (pattern : Ten) (guard : d487 pattern = 1) : d264 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2946 pattern childGuard
    simpa only [d264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2941 pattern childGuard
    simpa only [d264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2949 (pattern : Ten) (guard : d487 pattern = 1) : d265 pattern ≤ (0 : Int) + d492 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d265, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2947 pattern childGuard
    simpa only [d265, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d265, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2948 pattern childGuard
    simpa only [d265, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2950 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2951 (pattern : Ten) (guard : d384 pattern = 1) : d42 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2379 pattern childGuard
    simpa only [d384, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2950 pattern childGuard
    simpa only [d384, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2952 (pattern : Ten) (guard : d479 pattern = 1) : d48 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d479, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2856 pattern childGuard
    simpa only [d479, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d479, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2951 pattern childGuard
    simpa only [d479, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2953 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2954 (pattern : Ten) (guard : d480 pattern = 1) : d124 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d479 pattern = 1 := by simpa only [d480, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2952 pattern childGuard
    simpa only [d480, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d480, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2953 pattern childGuard
    simpa only [d480, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2955 (pattern : Ten) (guard : d0 pattern = 1) : d48 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2956 (pattern : Ten) (guard : d480 pattern = 1) : d48 pattern ≤ (2 : Int) + d455 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d479 pattern = 1 := by simpa only [d480, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2952 pattern childGuard
    simpa only [d480, d455, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d480, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2955 pattern childGuard
    simpa only [d480, d455, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2957 (pattern : Ten) (guard : d480 pattern = 1) : d125 pattern ≤ (2 : Int) + d495 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d125, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2954 pattern childGuard
    simpa only [d125, d495, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d125, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2956 pattern childGuard
    simpa only [d125, d495, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2958 (pattern : Ten) (guard : d0 pattern = 1) : d48 pattern ≤ (2 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2959 (pattern : Ten) (guard : d480 pattern = 1) : d48 pattern ≤ (2 : Int) + d496 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d479 pattern = 1 := by simpa only [d480, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2952 pattern childGuard
    simpa only [d480, d496, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d480, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2958 pattern childGuard
    simpa only [d480, d496, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2960 (pattern : Ten) (guard : d480 pattern = 1) : d48 pattern ≤ (2 : Int) + d497 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2959 pattern childGuard
    simpa only [d497, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2956 pattern childGuard
    simpa only [d497, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2961 (pattern : Ten) (guard : d480 pattern = 1) : d128 pattern ≤ (2 : Int) + d498 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d128, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2957 pattern childGuard
    simpa only [d128, d498, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d128, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2960 pattern childGuard
    simpa only [d128, d498, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2962 (pattern : Ten) (guard : d479 pattern = 1) : d20 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d479, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2852 pattern childGuard
    simpa only [d479, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d479, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2725 pattern childGuard
    simpa only [d479, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2963 (pattern : Ten) (guard : d0 pattern = 1) : d20 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2964 (pattern : Ten) (guard : d480 pattern = 1) : d20 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d479 pattern = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2962 pattern childGuard
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2963 pattern childGuard
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2965 (pattern : Ten) (guard : d480 pattern = 1) : d126 pattern ≤ (2 : Int) + d499 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d126, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2956 pattern childGuard
    simpa only [d126, d499, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d126, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2964 pattern childGuard
    simpa only [d126, d499, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2966 (pattern : Ten) (guard : d0 pattern = 1) : d44 pattern ≤ (2 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2967 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2968 (pattern : Ten) (guard : d384 pattern = 1) : d43 pattern ≤ (2 : Int) + d4 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2381 pattern childGuard
    simpa only [d384, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2967 pattern childGuard
    simpa only [d384, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2969 (pattern : Ten) (guard : d479 pattern = 1) : d50 pattern ≤ (2 : Int) + d4 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d479, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2966 pattern childGuard
    simpa only [d479, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d479, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2968 pattern childGuard
    simpa only [d479, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2970 (pattern : Ten) (guard : d0 pattern = 1) : d50 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2971 (pattern : Ten) (guard : d480 pattern = 1) : d50 pattern ≤ (2 : Int) + d500 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d479 pattern = 1 := by simpa only [d480, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2969 pattern childGuard
    simpa only [d480, d500, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d480, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2970 pattern childGuard
    simpa only [d480, d500, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2972 (pattern : Ten) (guard : d480 pattern = 1) : d127 pattern ≤ (2 : Int) + d501 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d127, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2971 pattern childGuard
    simpa only [d127, d501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d127, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2964 pattern childGuard
    simpa only [d127, d501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2973 (pattern : Ten) (guard : d480 pattern = 1) : d129 pattern ≤ (2 : Int) + d502 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d129, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2965 pattern childGuard
    simpa only [d129, d502, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d129, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2972 pattern childGuard
    simpa only [d129, d502, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2974 (pattern : Ten) (guard : d480 pattern = 1) : d130 pattern ≤ (2 : Int) + d503 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d130, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2961 pattern childGuard
    simpa only [d130, d503, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d130, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2973 pattern childGuard
    simpa only [d130, d503, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2975 (pattern : Ten) (guard : d480 pattern = 1) : d10 pattern ≤ (2 : Int) + d10 pattern := by
  omega
theorem c2976 (pattern : Ten) (guard : d480 pattern = 1) : d131 pattern ≤ (2 : Int) + d504 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d131, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2973 pattern childGuard
    simpa only [d131, d504, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d131, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2975 pattern childGuard
    simpa only [d131, d504, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2977 (pattern : Ten) (guard : d480 pattern = 1) : d132 pattern ≤ (2 : Int) + d505 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d480 pattern = 1 := by simpa only [d132, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2974 pattern childGuard
    simpa only [d132, d505, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d480 pattern = 1 := by simpa only [d132, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2976 pattern childGuard
    simpa only [d132, d505, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2978 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2979 (pattern : Ten) (guard : d383 pattern = 1) : d197 pattern ≤ (2 : Int) + d172 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2414 pattern childGuard
    simpa only [d383, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2978 pattern childGuard
    simpa only [d383, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2980 (pattern : Ten) (guard : d486 pattern = 1) : d202 pattern ≤ (2 : Int) + d172 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d486, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2884 pattern childGuard
    simpa only [d486, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d486, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2979 pattern childGuard
    simpa only [d486, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2981 (pattern : Ten) (guard : d487 pattern = 1) : d280 pattern ≤ (2 : Int) + d172 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d486 pattern = 1 := by simpa only [d487, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2980 pattern childGuard
    simpa only [d487, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d487, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2978 pattern childGuard
    simpa only [d487, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2982 (pattern : Ten) (guard : d0 pattern = 1) : d202 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2983 (pattern : Ten) (guard : d487 pattern = 1) : d202 pattern ≤ (2 : Int) + d463 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d486 pattern = 1 := by simpa only [d487, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2980 pattern childGuard
    simpa only [d487, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d487, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2982 pattern childGuard
    simpa only [d487, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2984 (pattern : Ten) (guard : d487 pattern = 1) : d281 pattern ≤ (2 : Int) + d507 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d281, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2981 pattern childGuard
    simpa only [d281, d507, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d281, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2983 pattern childGuard
    simpa only [d281, d507, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2985 (pattern : Ten) (guard : d0 pattern = 1) : d202 pattern ≤ (2 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2986 (pattern : Ten) (guard : d487 pattern = 1) : d202 pattern ≤ (2 : Int) + d508 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d486 pattern = 1 := by simpa only [d487, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2980 pattern childGuard
    simpa only [d487, d508, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d487, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2985 pattern childGuard
    simpa only [d487, d508, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2987 (pattern : Ten) (guard : d487 pattern = 1) : d202 pattern ≤ (2 : Int) + d509 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2986 pattern childGuard
    simpa only [d509, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2983 pattern childGuard
    simpa only [d509, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2988 (pattern : Ten) (guard : d487 pattern = 1) : d284 pattern ≤ (2 : Int) + d510 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d284, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2984 pattern childGuard
    simpa only [d284, d510, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d284, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2987 pattern childGuard
    simpa only [d284, d510, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2989 (pattern : Ten) (guard : d487 pattern = 1) : d10 pattern ≤ (2 : Int) + d10 pattern := by
  omega
theorem c2990 (pattern : Ten) (guard : d487 pattern = 1) : d282 pattern ≤ (2 : Int) + d464 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d282, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2983 pattern childGuard
    simpa only [d282, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d282, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2989 pattern childGuard
    simpa only [d282, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2991 (pattern : Ten) (guard : d0 pattern = 1) : d199 pattern ≤ (2 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2992 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2993 (pattern : Ten) (guard : d383 pattern = 1) : d198 pattern ≤ (2 : Int) + d193 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2418 pattern childGuard
    simpa only [d383, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2992 pattern childGuard
    simpa only [d383, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2994 (pattern : Ten) (guard : d486 pattern = 1) : d204 pattern ≤ (2 : Int) + d193 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d486, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2991 pattern childGuard
    simpa only [d486, d204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d486, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2993 pattern childGuard
    simpa only [d486, d204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2995 (pattern : Ten) (guard : d0 pattern = 1) : d204 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2996 (pattern : Ten) (guard : d487 pattern = 1) : d204 pattern ≤ (2 : Int) + d511 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d486 pattern = 1 := by simpa only [d487, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2994 pattern childGuard
    simpa only [d487, d511, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d487, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2995 pattern childGuard
    simpa only [d487, d511, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2997 (pattern : Ten) (guard : d487 pattern = 1) : d283 pattern ≤ (2 : Int) + d512 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d283, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2996 pattern childGuard
    simpa only [d283, d512, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d283, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2989 pattern childGuard
    simpa only [d283, d512, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2998 (pattern : Ten) (guard : d487 pattern = 1) : d285 pattern ≤ (2 : Int) + d513 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d285, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2990 pattern childGuard
    simpa only [d285, d513, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d285, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2997 pattern childGuard
    simpa only [d285, d513, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2999 (pattern : Ten) (guard : d487 pattern = 1) : d286 pattern ≤ (2 : Int) + d514 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d286, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2988 pattern childGuard
    simpa only [d286, d514, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d286, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2998 pattern childGuard
    simpa only [d286, d514, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3000 (pattern : Ten) (guard : d487 pattern = 1) : d287 pattern ≤ (2 : Int) + d515 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d287, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2998 pattern childGuard
    simpa only [d287, d515, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d287, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2989 pattern childGuard
    simpa only [d287, d515, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3001 (pattern : Ten) (guard : d487 pattern = 1) : d288 pattern ≤ (2 : Int) + d516 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d487 pattern = 1 := by simpa only [d288, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2999 pattern childGuard
    simpa only [d288, d516, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d487 pattern = 1 := by simpa only [d288, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3000 pattern childGuard
    simpa only [d288, d516, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3002 (pattern : Ten) (guard : d0 pattern = 1) : d108 pattern ≤ (0 : Int) + d48 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3003 (pattern : Ten) (guard : d518 pattern = 1) : d109 pattern ≤ (0 : Int) + d48 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d518, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3002 pattern childGuard
    simpa only [d518, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d389 pattern = 1 := by simpa only [d518, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c633 pattern childGuard
    simpa only [d518, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3004 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3005 (pattern : Ten) (guard : d518 pattern = 1) : d110 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d518, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3004 pattern childGuard
    simpa only [d518, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d389 pattern = 1 := by simpa only [d518, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c645 pattern childGuard
    simpa only [d518, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3006 (pattern : Ten) (guard : d518 pattern = 1) : d115 pattern ≤ (0 : Int) + d126 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d518 pattern = 1 := by simpa only [d115, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3003 pattern childGuard
    simpa only [d115, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d518 pattern = 1 := by simpa only [d115, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3005 pattern childGuard
    simpa only [d115, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3007 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d50 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3008 (pattern : Ten) (guard : d518 pattern = 1) : d111 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d518, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3007 pattern childGuard
    simpa only [d518, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d389 pattern = 1 := by simpa only [d518, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c650 pattern childGuard
    simpa only [d518, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3009 (pattern : Ten) (guard : d518 pattern = 1) : d116 pattern ≤ (0 : Int) + d127 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d518 pattern = 1 := by simpa only [d116, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3008 pattern childGuard
    simpa only [d116, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d518 pattern = 1 := by simpa only [d116, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3005 pattern childGuard
    simpa only [d116, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3010 (pattern : Ten) (guard : d518 pattern = 1) : d119 pattern ≤ (0 : Int) + d129 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d518 pattern = 1 := by simpa only [d119, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3006 pattern childGuard
    simpa only [d119, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d518 pattern = 1 := by simpa only [d119, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3009 pattern childGuard
    simpa only [d119, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3011 (pattern : Ten) (guard : d389 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c3012 (pattern : Ten) (guard : d518 pattern = 1) : d112 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d518, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c688 pattern childGuard
    simpa only [d518, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d389 pattern = 1 := by simpa only [d518, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3011 pattern childGuard
    simpa only [d518, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3013 (pattern : Ten) (guard : d518 pattern = 1) : d113 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d518, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c644 pattern childGuard
    simpa only [d518, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d389 pattern = 1 := by simpa only [d518, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3011 pattern childGuard
    simpa only [d518, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3014 (pattern : Ten) (guard : d518 pattern = 1) : d117 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d518 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3012 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d518 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3013 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3015 (pattern : Ten) (guard : d518 pattern = 1) : d114 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d518, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c699 pattern childGuard
    simpa only [d518, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d389 pattern = 1 := by simpa only [d518, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3011 pattern childGuard
    simpa only [d518, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3016 (pattern : Ten) (guard : d518 pattern = 1) : d118 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d518 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3015 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d518 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3013 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3017 (pattern : Ten) (guard : d518 pattern = 1) : d120 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d518 pattern = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3014 pattern childGuard
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d518 pattern = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3016 pattern childGuard
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3018 (pattern : Ten) (guard : d518 pattern = 1) : d121 pattern ≤ (0 : Int) + d131 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d518 pattern = 1 := by simpa only [d121, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3010 pattern childGuard
    simpa only [d121, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d518 pattern = 1 := by simpa only [d121, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3017 pattern childGuard
    simpa only [d121, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3019 (pattern : Ten) (guard : d0 pattern = 1) : d122 pattern ≤ (0 : Int) + d131 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3020 (pattern : Ten) (guard : d519 pattern = 1) : d123 pattern ≤ (0 : Int) + d131 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d518 pattern = 1 := by simpa only [d519, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3018 pattern childGuard
    simpa only [d519, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d519, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3019 pattern childGuard
    simpa only [d519, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3021 (pattern : Ten) (guard : d0 pattern = 1) : d266 pattern ≤ (0 : Int) + d202 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3022 (pattern : Ten) (guard : d520 pattern = 1) : d267 pattern ≤ (0 : Int) + d202 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d520, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3021 pattern childGuard
    simpa only [d520, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d386 pattern = 1 := by simpa only [d520, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c665 pattern childGuard
    simpa only [d520, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3023 (pattern : Ten) (guard : d386 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c3024 (pattern : Ten) (guard : d520 pattern = 1) : d268 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d520, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c662 pattern childGuard
    simpa only [d520, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d386 pattern = 1 := by simpa only [d520, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3023 pattern childGuard
    simpa only [d520, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3025 (pattern : Ten) (guard : d520 pattern = 1) : d271 pattern ≤ (0 : Int) + d282 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d520 pattern = 1 := by simpa only [d271, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3022 pattern childGuard
    simpa only [d271, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d520 pattern = 1 := by simpa only [d271, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3024 pattern childGuard
    simpa only [d271, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3026 (pattern : Ten) (guard : d0 pattern = 1) : d174 pattern ≤ (0 : Int) + d204 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3027 (pattern : Ten) (guard : d520 pattern = 1) : d269 pattern ≤ (0 : Int) + d204 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d520, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3026 pattern childGuard
    simpa only [d520, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d386 pattern = 1 := by simpa only [d520, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c677 pattern childGuard
    simpa only [d520, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3028 (pattern : Ten) (guard : d520 pattern = 1) : d272 pattern ≤ (0 : Int) + d283 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d520 pattern = 1 := by simpa only [d272, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3027 pattern childGuard
    simpa only [d272, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d520 pattern = 1 := by simpa only [d272, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3024 pattern childGuard
    simpa only [d272, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3029 (pattern : Ten) (guard : d520 pattern = 1) : d275 pattern ≤ (0 : Int) + d285 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d520 pattern = 1 := by simpa only [d275, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3025 pattern childGuard
    simpa only [d275, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d520 pattern = 1 := by simpa only [d275, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3028 pattern childGuard
    simpa only [d275, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3030 (pattern : Ten) (guard : d520 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c3031 (pattern : Ten) (guard : d520 pattern = 1) : d273 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d520 pattern = 1 := by simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3024 pattern childGuard
    simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d520 pattern = 1 := by simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3030 pattern childGuard
    simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3032 (pattern : Ten) (guard : d520 pattern = 1) : d270 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d520, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c722 pattern childGuard
    simpa only [d520, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d386 pattern = 1 := by simpa only [d520, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3023 pattern childGuard
    simpa only [d520, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3033 (pattern : Ten) (guard : d520 pattern = 1) : d274 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d520 pattern = 1 := by simpa only [d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3032 pattern childGuard
    simpa only [d274, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d520 pattern = 1 := by simpa only [d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3030 pattern childGuard
    simpa only [d274, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3034 (pattern : Ten) (guard : d520 pattern = 1) : d276 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d520 pattern = 1 := by simpa only [d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3031 pattern childGuard
    simpa only [d276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d520 pattern = 1 := by simpa only [d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3033 pattern childGuard
    simpa only [d276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3035 (pattern : Ten) (guard : d520 pattern = 1) : d277 pattern ≤ (0 : Int) + d287 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d520 pattern = 1 := by simpa only [d277, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3029 pattern childGuard
    simpa only [d277, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d520 pattern = 1 := by simpa only [d277, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3034 pattern childGuard
    simpa only [d277, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3036 (pattern : Ten) (guard : d0 pattern = 1) : d278 pattern ≤ (0 : Int) + d287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3037 (pattern : Ten) (guard : d521 pattern = 1) : d279 pattern ≤ (0 : Int) + d287 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d520 pattern = 1 := by simpa only [d521, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3035 pattern childGuard
    simpa only [d521, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d521, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3036 pattern childGuard
    simpa only [d521, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3038 (pattern : Ten) (guard : d0 pattern = 1) : d48 pattern ≤ (2 : Int) + d42 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3039 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d42 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban41.Diagram
