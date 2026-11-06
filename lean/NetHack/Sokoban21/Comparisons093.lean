/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons092
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c13020 (pattern : Twelve) (guard : d1 pattern = 1) : d102 pattern ≤ (5 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12992 pattern childGuard
    simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13019 pattern childGuard
    simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13021 (pattern : Twelve) (guard : d1 pattern = 1) : d76 pattern ≤ (5 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12964 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13017 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13022 (pattern : Twelve) (guard : d1 pattern = 1) : d93 pattern ≤ (5 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12971 pattern childGuard
    simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13021 pattern childGuard
    simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13023 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (5 : Int) + d56 pattern := by
  omega
theorem c13024 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (5 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12968 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13025 (pattern : Twelve) (guard : d1 pattern = 1) : d57 pattern ≤ (5 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13005 pattern childGuard
    simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13024 pattern childGuard
    simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13026 (pattern : Twelve) (guard : d1 pattern = 1) : d77 pattern ≤ (5 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13023 pattern childGuard
    simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13025 pattern childGuard
    simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13027 (pattern : Twelve) (guard : d1 pattern = 1) : d35 pattern ≤ (5 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12964 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13028 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (5 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13005 pattern childGuard
    simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13027 pattern childGuard
    simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13029 (pattern : Twelve) (guard : d1 pattern = 1) : d78 pattern ≤ (5 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13028 pattern childGuard
    simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13017 pattern childGuard
    simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13030 (pattern : Twelve) (guard : d1 pattern = 1) : d94 pattern ≤ (5 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13026 pattern childGuard
    simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13029 pattern childGuard
    simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13031 (pattern : Twelve) (guard : d1 pattern = 1) : d103 pattern ≤ (5 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13022 pattern childGuard
    simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13030 pattern childGuard
    simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13032 (pattern : Twelve) (guard : d1 pattern = 1) : d110 pattern ≤ (5 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13020 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13031 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13033 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (5 : Int) + d3 pattern := by
  omega
theorem c13034 (pattern : Twelve) (guard : d1 pattern = 1) : d37 pattern ≤ (5 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12968 pattern childGuard
    simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13033 pattern childGuard
    simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13035 (pattern : Twelve) (guard : d1 pattern = 1) : d58 pattern ≤ (5 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13005 pattern childGuard
    simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13034 pattern childGuard
    simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13036 (pattern : Twelve) (guard : d1 pattern = 1) : d79 pattern ≤ (5 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12993 pattern childGuard
    simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13035 pattern childGuard
    simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13037 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (5 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13005 pattern childGuard
    simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13017 pattern childGuard
    simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13038 (pattern : Twelve) (guard : d1 pattern = 1) : d95 pattern ≤ (5 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13036 pattern childGuard
    simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13037 pattern childGuard
    simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13039 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (5 : Int) + d59 pattern := by
  omega
theorem c13040 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (5 : Int) + d4 pattern := by
  omega
theorem c13041 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (5 : Int) + d5 pattern := by
  change (4 : Int) ≤ (5 : Int) + 5
  decide
theorem c13042 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (5 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13040 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13041 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13043 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (5 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13040 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13042 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13044 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (5 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13004 pattern childGuard
    simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13043 pattern childGuard
    simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13045 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (5 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12980 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13033 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13046 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (5 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13003 pattern childGuard
    simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13045 pattern childGuard
    simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13047 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (5 : Int) + d820 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13046 pattern childGuard
    simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13048 (pattern : Twelve) (guard : d1 pattern = 1) : d60 pattern ≤ (5 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13044 pattern childGuard
    simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13047 pattern childGuard
    simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13049 (pattern : Twelve) (guard : d1 pattern = 1) : d81 pattern ≤ (5 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13039 pattern childGuard
    simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13048 pattern childGuard
    simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13050 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (5 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13004 pattern childGuard
    simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13051 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (5 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13044 pattern childGuard
    simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13050 pattern childGuard
    simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13052 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (5 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13040 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12997 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13053 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (5 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13041 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12995 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13054 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (5 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13052 pattern childGuard
    simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13053 pattern childGuard
    simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13055 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (5 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13015 pattern childGuard
    simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13054 pattern childGuard
    simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13056 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (5 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12978 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12997 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13057 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (5 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12981 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12995 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13058 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (5 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13056 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13057 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13059 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (5 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13058 pattern childGuard
    simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13060 (pattern : Twelve) (guard : d1 pattern = 1) : d61 pattern ≤ (5 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13055 pattern childGuard
    simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13059 pattern childGuard
    simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13061 (pattern : Twelve) (guard : d1 pattern = 1) : d82 pattern ≤ (5 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13051 pattern childGuard
    simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13060 pattern childGuard
    simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13062 (pattern : Twelve) (guard : d1 pattern = 1) : d96 pattern ≤ (5 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13049 pattern childGuard
    simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13061 pattern childGuard
    simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13063 (pattern : Twelve) (guard : d1 pattern = 1) : d104 pattern ≤ (5 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13038 pattern childGuard
    simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13062 pattern childGuard
    simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13064 (pattern : Twelve) (guard : d1 pattern = 1) : d105 pattern ≤ (5 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13030 pattern childGuard
    simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13065 (pattern : Twelve) (guard : d1 pattern = 1) : d111 pattern ≤ (5 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13063 pattern childGuard
    simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13064 pattern childGuard
    simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13066 (pattern : Twelve) (guard : d1 pattern = 1) : d114 pattern ≤ (5 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13032 pattern childGuard
    simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13065 pattern childGuard
    simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13067 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (5 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12964 pattern childGuard
    simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13002 pattern childGuard
    simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13068 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (5 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13067 pattern childGuard
    simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13017 pattern childGuard
    simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13069 (pattern : Twelve) (guard : d1 pattern = 1) : d97 pattern ≤ (5 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12971 pattern childGuard
    simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13068 pattern childGuard
    simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13070 (pattern : Twelve) (guard : d1 pattern = 1) : d43 pattern ≤ (5 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12965 pattern childGuard
    simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13007 pattern childGuard
    simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13071 (pattern : Twelve) (guard : d1 pattern = 1) : d62 pattern ≤ (5 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13005 pattern childGuard
    simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13070 pattern childGuard
    simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13072 (pattern : Twelve) (guard : d1 pattern = 1) : d83 pattern ≤ (5 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13001 pattern childGuard
    simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13071 pattern childGuard
    simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13073 (pattern : Twelve) (guard : d1 pattern = 1) : d44 pattern ≤ (5 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13002 pattern childGuard
    simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13011 pattern childGuard
    simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13074 (pattern : Twelve) (guard : d1 pattern = 1) : d63 pattern ≤ (5 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13005 pattern childGuard
    simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13073 pattern childGuard
    simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13075 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (5 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13015 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13076 (pattern : Twelve) (guard : d1 pattern = 1) : d64 pattern ≤ (5 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13016 pattern childGuard
    simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13075 pattern childGuard
    simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13077 (pattern : Twelve) (guard : d1 pattern = 1) : d84 pattern ≤ (5 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13074 pattern childGuard
    simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13076 pattern childGuard
    simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13078 (pattern : Twelve) (guard : d1 pattern = 1) : d98 pattern ≤ (5 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13072 pattern childGuard
    simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13077 pattern childGuard
    simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13079 (pattern : Twelve) (guard : d1 pattern = 1) : d106 pattern ≤ (5 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13069 pattern childGuard
    simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13078 pattern childGuard
    simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13080 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (5 : Int) + d45 pattern := by
  omega
theorem c13081 (pattern : Twelve) (guard : d1 pattern = 1) : d65 pattern ≤ (5 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13005 pattern childGuard
    simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13080 pattern childGuard
    simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13082 (pattern : Twelve) (guard : d1 pattern = 1) : d85 pattern ≤ (5 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13023 pattern childGuard
    simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13081 pattern childGuard
    simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13083 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (5 : Int) + d39 pattern := by
  omega
theorem c13084 (pattern : Twelve) (guard : d1 pattern = 1) : d66 pattern ≤ (5 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13005 pattern childGuard
    simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13083 pattern childGuard
    simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13085 (pattern : Twelve) (guard : d1 pattern = 1) : d86 pattern ≤ (5 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13084 pattern childGuard
    simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13076 pattern childGuard
    simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13086 (pattern : Twelve) (guard : d1 pattern = 1) : d99 pattern ≤ (5 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13082 pattern childGuard
    simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13085 pattern childGuard
    simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13087 (pattern : Twelve) (guard : d1 pattern = 1) : d107 pattern ≤ (5 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13069 pattern childGuard
    simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13086 pattern childGuard
    simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13088 (pattern : Twelve) (guard : d1 pattern = 1) : d112 pattern ≤ (5 : Int) + d864 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13079 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13087 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13089 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (5 : Int) + d46 pattern := by
  omega
theorem c13090 (pattern : Twelve) (guard : d1 pattern = 1) : d67 pattern ≤ (5 : Int) + d834 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13005 pattern childGuard
    simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13089 pattern childGuard
    simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13091 (pattern : Twelve) (guard : d1 pattern = 1) : d87 pattern ≤ (5 : Int) + d849 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12993 pattern childGuard
    simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13090 pattern childGuard
    simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13092 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (5 : Int) + d38 pattern := by
  omega
theorem c13093 (pattern : Twelve) (guard : d1 pattern = 1) : d68 pattern ≤ (5 : Int) + d835 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13005 pattern childGuard
    simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13092 pattern childGuard
    simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13094 (pattern : Twelve) (guard : d1 pattern = 1) : d88 pattern ≤ (5 : Int) + d850 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13093 pattern childGuard
    simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13076 pattern childGuard
    simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13095 (pattern : Twelve) (guard : d1 pattern = 1) : d100 pattern ≤ (5 : Int) + d859 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13091 pattern childGuard
    simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13094 pattern childGuard
    simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13096 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (5 : Int) + d47 pattern := by
  omega
theorem c13097 (pattern : Twelve) (guard : d1 pattern = 1) : d69 pattern ≤ (5 : Int) + d836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13044 pattern childGuard
    simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13096 pattern childGuard
    simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13098 (pattern : Twelve) (guard : d1 pattern = 1) : d89 pattern ≤ (5 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13039 pattern childGuard
    simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13097 pattern childGuard
    simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13099 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (5 : Int) + d48 pattern := by
  omega
theorem c13100 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (5 : Int) + d837 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13044 pattern childGuard
    simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13099 pattern childGuard
    simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13101 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (5 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13054 pattern childGuard
    simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13102 (pattern : Twelve) (guard : d1 pattern = 1) : d71 pattern ≤ (5 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13055 pattern childGuard
    simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13101 pattern childGuard
    simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13103 (pattern : Twelve) (guard : d1 pattern = 1) : d90 pattern ≤ (5 : Int) + d852 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13100 pattern childGuard
    simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13102 pattern childGuard
    simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13104 (pattern : Twelve) (guard : d1 pattern = 1) : d101 pattern ≤ (5 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13098 pattern childGuard
    simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13103 pattern childGuard
    simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13105 (pattern : Twelve) (guard : d1 pattern = 1) : d108 pattern ≤ (5 : Int) + d865 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13095 pattern childGuard
    simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13104 pattern childGuard
    simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13106 (pattern : Twelve) (guard : d1 pattern = 1) : d109 pattern ≤ (5 : Int) + d866 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13086 pattern childGuard
    simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13107 (pattern : Twelve) (guard : d1 pattern = 1) : d113 pattern ≤ (5 : Int) + d868 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13105 pattern childGuard
    simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13106 pattern childGuard
    simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13108 (pattern : Twelve) (guard : d1 pattern = 1) : d115 pattern ≤ (5 : Int) + d870 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13088 pattern childGuard
    simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13107 pattern childGuard
    simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13109 (pattern : Twelve) (guard : d1 pattern = 1) : d116 pattern ≤ (5 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13066 pattern childGuard
    simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13108 pattern childGuard
    simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13110 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (5 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12962 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12977 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13111 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (5 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12963 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13110 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13112 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (5 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12965 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12977 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13113 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (5 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12965 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13112 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13114 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (5 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13111 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13113 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13115 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (5 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12967 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13112 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13116 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (5 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13115 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13113 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13117 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (5 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13114 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13116 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13118 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (5 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12964 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13117 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13119 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (5 : Int) + d6 pattern := by
  change (0 : Int) ≤ (5 : Int) + 6
  decide
theorem c13120 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (5 : Int) + d6 pattern := by
  change (2 : Int) ≤ (5 : Int) + 6
  decide
theorem c13121 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13119 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13120 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13122 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (5 : Int) + d6 pattern := by
  change (1 : Int) ≤ (5 : Int) + 6
  decide
theorem c13123 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13122 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12994 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13124 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13121 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13123 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13125 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13120 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12997 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13126 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13125 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12996 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13127 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13124 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13126 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13128 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13126 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13129 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13127 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13128 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13130 (pattern : Twelve) (guard : d1 pattern = 1) : d839 pattern ≤ (5 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12976 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13129 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13131 (pattern : Twelve) (guard : d1 pattern = 1) : d853 pattern ≤ (5 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13118 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13130 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13132 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (5 : Int) + d4 pattern := by
  change (3 : Int) ≤ (5 : Int) + 4
  decide
theorem c13133 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (5 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12980 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13132 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13134 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (5 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13003 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13133 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13135 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (5 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13111 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13134 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13136 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (5 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13115 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13137 (pattern : Twelve) (guard : d1 pattern = 1) : d826 pattern ≤ (5 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13135 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13136 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13138 (pattern : Twelve) (guard : d1 pattern = 1) : d840 pattern ≤ (5 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13028 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13137 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13139 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (5 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12976 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13140 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (5 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13016 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13139 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13141 (pattern : Twelve) (guard : d1 pattern = 1) : d841 pattern ≤ (5 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13140 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13129 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13142 (pattern : Twelve) (guard : d1 pattern = 1) : d854 pattern ≤ (5 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13138 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13141 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13143 (pattern : Twelve) (guard : d1 pattern = 1) : d861 pattern ≤ (5 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13131 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13142 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13144 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (5 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13033 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13132 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13145 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (5 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13033 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13144 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13146 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (5 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13115 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13145 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13147 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (5 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13135 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13146 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13148 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (5 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13005 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13147 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13149 (pattern : Twelve) (guard : d1 pattern = 1) : d843 pattern ≤ (5 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13016 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13129 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13150 (pattern : Twelve) (guard : d1 pattern = 1) : d855 pattern ≤ (5 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13148 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13149 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13151 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (5 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13042 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13053 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13152 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (5 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13134 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13151 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13153 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (5 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13045 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13144 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13154 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (5 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13153 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13155 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (5 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13152 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13154 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13156 (pattern : Twelve) (guard : d1 pattern = 1) : d844 pattern ≤ (5 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13051 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13155 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13157 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (5 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13055 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13075 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13158 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13126 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13007 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13159 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13007 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
