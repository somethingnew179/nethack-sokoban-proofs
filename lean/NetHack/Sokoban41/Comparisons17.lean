/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons16
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c2720 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2721 (pattern : Ten) (guard : d384 pattern = 1) : d86 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2719 pattern childGuard
    simpa only [d384, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2720 pattern childGuard
    simpa only [d384, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2722 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2723 (pattern : Ten) (guard : d384 pattern = 1) : d0 pattern ≤ (2 : Int) + d12 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2719 pattern childGuard
    simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2722 pattern childGuard
    simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2724 (pattern : Ten) (guard : d384 pattern = 1) : d87 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d87, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2721 pattern childGuard
    simpa only [d87, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d87, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2723 pattern childGuard
    simpa only [d87, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2725 (pattern : Ten) (guard : d384 pattern = 1) : d10 pattern ≤ (2 : Int) + d10 pattern := by
  omega
theorem c2726 (pattern : Ten) (guard : d384 pattern = 1) : d88 pattern ≤ (2 : Int) + d18 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d88, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2723 pattern childGuard
    simpa only [d88, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d88, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2725 pattern childGuard
    simpa only [d88, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2727 (pattern : Ten) (guard : d384 pattern = 1) : d93 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d93, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2724 pattern childGuard
    simpa only [d93, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d93, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2726 pattern childGuard
    simpa only [d93, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2728 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (2 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2729 (pattern : Ten) (guard : d384 pattern = 1) : d0 pattern ≤ (2 : Int) + d13 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2719 pattern childGuard
    simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2728 pattern childGuard
    simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2730 (pattern : Ten) (guard : d350 pattern = 1) : d11 pattern ≤ (2 : Int) + d11 pattern := by
  omega
theorem c2731 (pattern : Ten) (guard : d384 pattern = 1) : d11 pattern ≤ (2 : Int) + d14 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2730 pattern childGuard
    simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1973 pattern childGuard
    simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2732 (pattern : Ten) (guard : d384 pattern = 1) : d89 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d89, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2729 pattern childGuard
    simpa only [d89, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d89, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2731 pattern childGuard
    simpa only [d89, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2733 (pattern : Ten) (guard : d384 pattern = 1) : d90 pattern ≤ (2 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d90, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2731 pattern childGuard
    simpa only [d90, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d90, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2725 pattern childGuard
    simpa only [d90, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2734 (pattern : Ten) (guard : d384 pattern = 1) : d94 pattern ≤ (2 : Int) + d24 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d94, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2732 pattern childGuard
    simpa only [d94, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d94, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2733 pattern childGuard
    simpa only [d94, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2735 (pattern : Ten) (guard : d384 pattern = 1) : d99 pattern ≤ (2 : Int) + d29 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d99, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2727 pattern childGuard
    simpa only [d99, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d99, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2734 pattern childGuard
    simpa only [d99, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2736 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (2 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2737 (pattern : Ten) (guard : d384 pattern = 1) : d0 pattern ≤ (2 : Int) + d15 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2719 pattern childGuard
    simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2736 pattern childGuard
    simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2738 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (2 : Int) + d2 pattern := by
  omega
theorem c2739 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2740 (pattern : Ten) (guard : d384 pattern = 1) : d2 pattern ≤ (2 : Int) + d16 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2738 pattern childGuard
    simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2739 pattern childGuard
    simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2741 (pattern : Ten) (guard : d384 pattern = 1) : d91 pattern ≤ (2 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d91, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2737 pattern childGuard
    simpa only [d91, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d91, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2740 pattern childGuard
    simpa only [d91, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2742 (pattern : Ten) (guard : d384 pattern = 1) : d92 pattern ≤ (2 : Int) + d22 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d92, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2740 pattern childGuard
    simpa only [d92, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d92, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2725 pattern childGuard
    simpa only [d92, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2743 (pattern : Ten) (guard : d384 pattern = 1) : d95 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d95, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2741 pattern childGuard
    simpa only [d95, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d95, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2742 pattern childGuard
    simpa only [d95, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2744 (pattern : Ten) (guard : d384 pattern = 1) : d100 pattern ≤ (2 : Int) + d30 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d100, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2743 pattern childGuard
    simpa only [d100, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d100, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2734 pattern childGuard
    simpa only [d100, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2745 (pattern : Ten) (guard : d384 pattern = 1) : d103 pattern ≤ (2 : Int) + d33 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d103, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2735 pattern childGuard
    simpa only [d103, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d103, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2744 pattern childGuard
    simpa only [d103, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2746 (pattern : Ten) (guard : d384 pattern = 1) : d96 pattern ≤ (2 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d96, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2726 pattern childGuard
    simpa only [d96, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d96, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2725 pattern childGuard
    simpa only [d96, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2747 (pattern : Ten) (guard : d384 pattern = 1) : d97 pattern ≤ (2 : Int) + d27 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d97, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2733 pattern childGuard
    simpa only [d97, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d97, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2725 pattern childGuard
    simpa only [d97, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2748 (pattern : Ten) (guard : d384 pattern = 1) : d101 pattern ≤ (2 : Int) + d31 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d101, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2746 pattern childGuard
    simpa only [d101, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d101, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2747 pattern childGuard
    simpa only [d101, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2749 (pattern : Ten) (guard : d384 pattern = 1) : d98 pattern ≤ (2 : Int) + d28 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d98, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2742 pattern childGuard
    simpa only [d98, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d98, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2725 pattern childGuard
    simpa only [d98, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2750 (pattern : Ten) (guard : d384 pattern = 1) : d102 pattern ≤ (2 : Int) + d32 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d102, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2749 pattern childGuard
    simpa only [d102, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d102, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2747 pattern childGuard
    simpa only [d102, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2751 (pattern : Ten) (guard : d384 pattern = 1) : d104 pattern ≤ (2 : Int) + d34 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d104, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2748 pattern childGuard
    simpa only [d104, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d104, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2750 pattern childGuard
    simpa only [d104, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2752 (pattern : Ten) (guard : d384 pattern = 1) : d105 pattern ≤ (2 : Int) + d35 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d105, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2745 pattern childGuard
    simpa only [d105, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d105, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2751 pattern childGuard
    simpa only [d105, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2753 (pattern : Ten) (guard : d384 pattern = 1) : d106 pattern ≤ (2 : Int) + d36 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d106, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2751 pattern childGuard
    simpa only [d106, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d106, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2725 pattern childGuard
    simpa only [d106, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2754 (pattern : Ten) (guard : d384 pattern = 1) : d107 pattern ≤ (2 : Int) + d37 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d107, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2752 pattern childGuard
    simpa only [d107, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d107, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2753 pattern childGuard
    simpa only [d107, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2755 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (2 : Int) + d171 pattern := by
  omega
theorem c2756 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2757 (pattern : Ten) (guard : d383 pattern = 1) : d173 pattern ≤ (2 : Int) + d171 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2755 pattern childGuard
    simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2756 pattern childGuard
    simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2758 (pattern : Ten) (guard : d0 pattern = 1) : d171 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2759 (pattern : Ten) (guard : d383 pattern = 1) : d171 pattern ≤ (2 : Int) + d173 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2755 pattern childGuard
    simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2758 pattern childGuard
    simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2760 (pattern : Ten) (guard : d383 pattern = 1) : d249 pattern ≤ (2 : Int) + d176 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d249, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2757 pattern childGuard
    simpa only [d249, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d249, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2759 pattern childGuard
    simpa only [d249, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2761 (pattern : Ten) (guard : d383 pattern = 1) : d10 pattern ≤ (2 : Int) + d10 pattern := by
  omega
theorem c2762 (pattern : Ten) (guard : d383 pattern = 1) : d250 pattern ≤ (2 : Int) + d177 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d250, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2759 pattern childGuard
    simpa only [d250, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d250, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2761 pattern childGuard
    simpa only [d250, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2763 (pattern : Ten) (guard : d383 pattern = 1) : d253 pattern ≤ (2 : Int) + d180 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d253, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2760 pattern childGuard
    simpa only [d253, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d253, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2762 pattern childGuard
    simpa only [d253, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2764 (pattern : Ten) (guard : d383 pattern = 1) : d254 pattern ≤ (2 : Int) + d181 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d254, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2762 pattern childGuard
    simpa only [d254, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d254, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2761 pattern childGuard
    simpa only [d254, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2765 (pattern : Ten) (guard : d383 pattern = 1) : d257 pattern ≤ (2 : Int) + d184 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d257, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2763 pattern childGuard
    simpa only [d257, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d257, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2764 pattern childGuard
    simpa only [d257, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2766 (pattern : Ten) (guard : d0 pattern = 1) : d171 pattern ≤ (2 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2767 (pattern : Ten) (guard : d383 pattern = 1) : d171 pattern ≤ (2 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2755 pattern childGuard
    simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2766 pattern childGuard
    simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2768 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (2 : Int) + d172 pattern := by
  omega
theorem c2769 (pattern : Ten) (guard : d0 pattern = 1) : d172 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2770 (pattern : Ten) (guard : d383 pattern = 1) : d172 pattern ≤ (2 : Int) + d175 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2768 pattern childGuard
    simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2769 pattern childGuard
    simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2771 (pattern : Ten) (guard : d383 pattern = 1) : d251 pattern ≤ (2 : Int) + d178 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d251, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2767 pattern childGuard
    simpa only [d251, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d251, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2770 pattern childGuard
    simpa only [d251, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2772 (pattern : Ten) (guard : d383 pattern = 1) : d252 pattern ≤ (2 : Int) + d179 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d252, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2770 pattern childGuard
    simpa only [d252, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d252, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2761 pattern childGuard
    simpa only [d252, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2773 (pattern : Ten) (guard : d383 pattern = 1) : d255 pattern ≤ (2 : Int) + d182 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d255, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2771 pattern childGuard
    simpa only [d255, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d255, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2772 pattern childGuard
    simpa only [d255, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2774 (pattern : Ten) (guard : d383 pattern = 1) : d258 pattern ≤ (2 : Int) + d185 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d258, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2773 pattern childGuard
    simpa only [d258, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d258, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2764 pattern childGuard
    simpa only [d258, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2775 (pattern : Ten) (guard : d383 pattern = 1) : d261 pattern ≤ (2 : Int) + d188 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d261, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2765 pattern childGuard
    simpa only [d261, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d261, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2774 pattern childGuard
    simpa only [d261, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2776 (pattern : Ten) (guard : d383 pattern = 1) : d259 pattern ≤ (2 : Int) + d186 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d259, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2764 pattern childGuard
    simpa only [d259, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d259, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2761 pattern childGuard
    simpa only [d259, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2777 (pattern : Ten) (guard : d383 pattern = 1) : d256 pattern ≤ (2 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d256, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2772 pattern childGuard
    simpa only [d256, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d256, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2761 pattern childGuard
    simpa only [d256, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2778 (pattern : Ten) (guard : d383 pattern = 1) : d260 pattern ≤ (2 : Int) + d187 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d260, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2777 pattern childGuard
    simpa only [d260, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d260, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2761 pattern childGuard
    simpa only [d260, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2779 (pattern : Ten) (guard : d383 pattern = 1) : d262 pattern ≤ (2 : Int) + d189 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d262, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2776 pattern childGuard
    simpa only [d262, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d262, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2778 pattern childGuard
    simpa only [d262, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2780 (pattern : Ten) (guard : d383 pattern = 1) : d263 pattern ≤ (2 : Int) + d190 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d263, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2775 pattern childGuard
    simpa only [d263, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d263, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2779 pattern childGuard
    simpa only [d263, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2781 (pattern : Ten) (guard : d383 pattern = 1) : d264 pattern ≤ (2 : Int) + d191 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d264, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2779 pattern childGuard
    simpa only [d264, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d264, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2761 pattern childGuard
    simpa only [d264, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2782 (pattern : Ten) (guard : d383 pattern = 1) : d265 pattern ≤ (2 : Int) + d192 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d265, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2780 pattern childGuard
    simpa only [d265, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d265, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2781 pattern childGuard
    simpa only [d265, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2783 (pattern : Ten) (guard : d450 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c2784 (pattern : Ten) (guard : d0 pattern = 1) : d12 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2785 (pattern : Ten) (guard : d451 pattern = 1) : d17 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d450 pattern = 1 := by simpa only [d451, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2783 pattern childGuard
    simpa only [d451, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d451, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2784 pattern childGuard
    simpa only [d451, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2786 (pattern : Ten) (guard : d450 pattern = 1) : d12 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d450, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c90 pattern childGuard
    simpa only [d450, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d450, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d450, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2787 (pattern : Ten) (guard : d451 pattern = 1) : d18 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d450 pattern = 1 := by simpa only [d451, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2786 pattern childGuard
    simpa only [d451, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d451, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d451, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2788 (pattern : Ten) (guard : d451 pattern = 1) : d23 pattern ≤ (0 : Int) + d452 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d23, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2785 pattern childGuard
    simpa only [d23, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d23, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2787 pattern childGuard
    simpa only [d23, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2789 (pattern : Ten) (guard : d450 pattern = 1) : d13 pattern ≤ (0 : Int) + d11 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d450, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c607 pattern childGuard
    simpa only [d450, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d450, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c403 pattern childGuard
    simpa only [d450, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2790 (pattern : Ten) (guard : d0 pattern = 1) : d14 pattern ≤ (0 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2791 (pattern : Ten) (guard : d451 pattern = 1) : d19 pattern ≤ (0 : Int) + d11 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d450 pattern = 1 := by simpa only [d451, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2789 pattern childGuard
    simpa only [d451, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d451, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2790 pattern childGuard
    simpa only [d451, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2792 (pattern : Ten) (guard : d450 pattern = 1) : d14 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d450, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c462 pattern childGuard
    simpa only [d450, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d450, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d450, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2793 (pattern : Ten) (guard : d451 pattern = 1) : d20 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d450 pattern = 1 := by simpa only [d451, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2792 pattern childGuard
    simpa only [d451, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d451, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d451, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2794 (pattern : Ten) (guard : d451 pattern = 1) : d24 pattern ≤ (0 : Int) + d453 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d24, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2791 pattern childGuard
    simpa only [d24, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d24, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2793 pattern childGuard
    simpa only [d24, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2795 (pattern : Ten) (guard : d451 pattern = 1) : d29 pattern ≤ (0 : Int) + d454 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d29, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2788 pattern childGuard
    simpa only [d29, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d29, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2794 pattern childGuard
    simpa only [d29, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2796 (pattern : Ten) (guard : d450 pattern = 1) : d15 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d450, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c503 pattern childGuard
    simpa only [d450, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d450, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c412 pattern childGuard
    simpa only [d450, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2797 (pattern : Ten) (guard : d0 pattern = 1) : d16 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2798 (pattern : Ten) (guard : d451 pattern = 1) : d21 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d450 pattern = 1 := by simpa only [d451, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2796 pattern childGuard
    simpa only [d451, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d451, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2797 pattern childGuard
    simpa only [d451, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2799 (pattern : Ten) (guard : d450 pattern = 1) : d16 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d450, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c469 pattern childGuard
    simpa only [d450, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d450, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d450, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2800 (pattern : Ten) (guard : d451 pattern = 1) : d22 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d450 pattern = 1 := by simpa only [d451, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2799 pattern childGuard
    simpa only [d451, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d451, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d451, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2801 (pattern : Ten) (guard : d451 pattern = 1) : d25 pattern ≤ (0 : Int) + d455 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d25, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2798 pattern childGuard
    simpa only [d25, d455, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d25, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2800 pattern childGuard
    simpa only [d25, d455, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2802 (pattern : Ten) (guard : d451 pattern = 1) : d30 pattern ≤ (0 : Int) + d456 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d30, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2801 pattern childGuard
    simpa only [d30, d456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d30, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2794 pattern childGuard
    simpa only [d30, d456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2803 (pattern : Ten) (guard : d451 pattern = 1) : d33 pattern ≤ (0 : Int) + d457 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d33, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d33, d457, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d33, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2802 pattern childGuard
    simpa only [d33, d457, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2804 (pattern : Ten) (guard : d451 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c2805 (pattern : Ten) (guard : d451 pattern = 1) : d26 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2787 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2804 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2806 (pattern : Ten) (guard : d451 pattern = 1) : d27 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2793 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2804 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2807 (pattern : Ten) (guard : d451 pattern = 1) : d31 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2805 pattern childGuard
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2806 pattern childGuard
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2808 (pattern : Ten) (guard : d451 pattern = 1) : d28 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2800 pattern childGuard
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2804 pattern childGuard
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2809 (pattern : Ten) (guard : d451 pattern = 1) : d32 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2808 pattern childGuard
    simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2806 pattern childGuard
    simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2810 (pattern : Ten) (guard : d451 pattern = 1) : d34 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2807 pattern childGuard
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2809 pattern childGuard
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2811 (pattern : Ten) (guard : d451 pattern = 1) : d35 pattern ≤ (0 : Int) + d458 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d35, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2803 pattern childGuard
    simpa only [d35, d458, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d35, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2810 pattern childGuard
    simpa only [d35, d458, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2812 (pattern : Ten) (guard : d451 pattern = 1) : d36 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2810 pattern childGuard
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2804 pattern childGuard
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2813 (pattern : Ten) (guard : d451 pattern = 1) : d37 pattern ≤ (0 : Int) + d459 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d37, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2811 pattern childGuard
    simpa only [d37, d459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d37, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2812 pattern childGuard
    simpa only [d37, d459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2814 (pattern : Ten) (guard : d385 pattern = 1) : d171 pattern ≤ (0 : Int) + d171 pattern := by
  omega
theorem c2815 (pattern : Ten) (guard : d0 pattern = 1) : d173 pattern ≤ (0 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2816 (pattern : Ten) (guard : d460 pattern = 1) : d176 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d385 pattern = 1 := by simpa only [d460, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2814 pattern childGuard
    simpa only [d460, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d460, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2815 pattern childGuard
    simpa only [d460, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2817 (pattern : Ten) (guard : d385 pattern = 1) : d173 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d385, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c429 pattern childGuard
    simpa only [d385, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d385, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2126 pattern childGuard
    simpa only [d385, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2818 (pattern : Ten) (guard : d460 pattern = 1) : d177 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d385 pattern = 1 := by simpa only [d460, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2817 pattern childGuard
    simpa only [d460, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d460, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d460, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2819 (pattern : Ten) (guard : d460 pattern = 1) : d180 pattern ≤ (0 : Int) + d461 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d180, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2816 pattern childGuard
    simpa only [d180, d461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d180, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2818 pattern childGuard
    simpa only [d180, d461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2820 (pattern : Ten) (guard : d460 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c2821 (pattern : Ten) (guard : d460 pattern = 1) : d181 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2818 pattern childGuard
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2820 pattern childGuard
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2822 (pattern : Ten) (guard : d460 pattern = 1) : d184 pattern ≤ (0 : Int) + d462 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d184, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2819 pattern childGuard
    simpa only [d184, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d184, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2821 pattern childGuard
    simpa only [d184, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2823 (pattern : Ten) (guard : d385 pattern = 1) : d174 pattern ≤ (0 : Int) + d172 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d385, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c536 pattern childGuard
    simpa only [d385, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d385, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c441 pattern childGuard
    simpa only [d385, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2824 (pattern : Ten) (guard : d0 pattern = 1) : d175 pattern ≤ (0 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2825 (pattern : Ten) (guard : d460 pattern = 1) : d178 pattern ≤ (0 : Int) + d172 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d385 pattern = 1 := by simpa only [d460, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2823 pattern childGuard
    simpa only [d460, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d460, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2824 pattern childGuard
    simpa only [d460, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2826 (pattern : Ten) (guard : d385 pattern = 1) : d175 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d385, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c487 pattern childGuard
    simpa only [d385, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d385, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2126 pattern childGuard
    simpa only [d385, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2827 (pattern : Ten) (guard : d460 pattern = 1) : d179 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d385 pattern = 1 := by simpa only [d460, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2826 pattern childGuard
    simpa only [d460, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d460, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d460, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2828 (pattern : Ten) (guard : d460 pattern = 1) : d182 pattern ≤ (0 : Int) + d463 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d182, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2825 pattern childGuard
    simpa only [d182, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d182, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2827 pattern childGuard
    simpa only [d182, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2829 (pattern : Ten) (guard : d460 pattern = 1) : d185 pattern ≤ (0 : Int) + d464 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d185, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2828 pattern childGuard
    simpa only [d185, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d185, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2821 pattern childGuard
    simpa only [d185, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2830 (pattern : Ten) (guard : d460 pattern = 1) : d188 pattern ≤ (0 : Int) + d465 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d188, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2822 pattern childGuard
    simpa only [d188, d465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d188, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2829 pattern childGuard
    simpa only [d188, d465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2831 (pattern : Ten) (guard : d460 pattern = 1) : d186 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2821 pattern childGuard
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2820 pattern childGuard
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2832 (pattern : Ten) (guard : d460 pattern = 1) : d183 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2827 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2820 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2833 (pattern : Ten) (guard : d460 pattern = 1) : d187 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2832 pattern childGuard
    simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2820 pattern childGuard
    simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2834 (pattern : Ten) (guard : d460 pattern = 1) : d189 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2833 pattern childGuard
    simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2835 (pattern : Ten) (guard : d460 pattern = 1) : d190 pattern ≤ (0 : Int) + d466 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d190, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2830 pattern childGuard
    simpa only [d190, d466, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d190, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2834 pattern childGuard
    simpa only [d190, d466, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2836 (pattern : Ten) (guard : d460 pattern = 1) : d191 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2834 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2820 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2837 (pattern : Ten) (guard : d460 pattern = 1) : d192 pattern ≤ (0 : Int) + d467 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d460 pattern = 1 := by simpa only [d192, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2835 pattern childGuard
    simpa only [d192, d467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d460 pattern = 1 := by simpa only [d192, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2836 pattern childGuard
    simpa only [d192, d467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2838 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2839 (pattern : Ten) (guard : d450 pattern = 1) : d15 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d450, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2838 pattern childGuard
    simpa only [d450, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d450, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2378 pattern childGuard
    simpa only [d450, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2840 (pattern : Ten) (guard : d0 pattern = 1) : d5 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2841 (pattern : Ten) (guard : d451 pattern = 1) : d108 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d450 pattern = 1 := by simpa only [d451, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2839 pattern childGuard
    simpa only [d451, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d451, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2840 pattern childGuard
    simpa only [d451, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2842 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2843 (pattern : Ten) (guard : d451 pattern = 1) : d15 pattern ≤ (2 : Int) + d88 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d450 pattern = 1 := by simpa only [d451, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2839 pattern childGuard
    simpa only [d451, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d451, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2842 pattern childGuard
    simpa only [d451, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2844 (pattern : Ten) (guard : d451 pattern = 1) : d109 pattern ≤ (2 : Int) + d468 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d109, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2841 pattern childGuard
    simpa only [d109, d468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d109, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d109, d468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2845 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (2 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2846 (pattern : Ten) (guard : d451 pattern = 1) : d15 pattern ≤ (2 : Int) + d89 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d450 pattern = 1 := by simpa only [d451, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2839 pattern childGuard
    simpa only [d451, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d451, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2845 pattern childGuard
    simpa only [d451, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2847 (pattern : Ten) (guard : d0 pattern = 1) : d11 pattern ≤ (2 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2848 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d11 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2433 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2849 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2850 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (2 : Int) + d11 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2848 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2849 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2851 (pattern : Ten) (guard : d450 pattern = 1) : d14 pattern ≤ (2 : Int) + d11 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d450, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2847 pattern childGuard
    simpa only [d450, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d450, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2850 pattern childGuard
    simpa only [d450, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2852 (pattern : Ten) (guard : d0 pattern = 1) : d14 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2853 (pattern : Ten) (guard : d451 pattern = 1) : d14 pattern ≤ (2 : Int) + d90 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d450 pattern = 1 := by simpa only [d451, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2851 pattern childGuard
    simpa only [d451, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d451, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2852 pattern childGuard
    simpa only [d451, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2854 (pattern : Ten) (guard : d451 pattern = 1) : d110 pattern ≤ (2 : Int) + d94 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d110, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2846 pattern childGuard
    simpa only [d110, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d110, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d110, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2855 (pattern : Ten) (guard : d451 pattern = 1) : d115 pattern ≤ (2 : Int) + d469 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d115, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2844 pattern childGuard
    simpa only [d115, d469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d115, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2854 pattern childGuard
    simpa only [d115, d469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2856 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (2 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2857 (pattern : Ten) (guard : d451 pattern = 1) : d15 pattern ≤ (2 : Int) + d91 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d450 pattern = 1 := by simpa only [d451, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2839 pattern childGuard
    simpa only [d451, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d451, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2856 pattern childGuard
    simpa only [d451, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2858 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (2 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2859 (pattern : Ten) (guard : d450 pattern = 1) : d44 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d450, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2858 pattern childGuard
    simpa only [d450, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d450, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2379 pattern childGuard
    simpa only [d450, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2860 (pattern : Ten) (guard : d0 pattern = 1) : d44 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2861 (pattern : Ten) (guard : d451 pattern = 1) : d44 pattern ≤ (2 : Int) + d92 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d450 pattern = 1 := by simpa only [d451, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2859 pattern childGuard
    simpa only [d451, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d451, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2860 pattern childGuard
    simpa only [d451, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2862 (pattern : Ten) (guard : d451 pattern = 1) : d111 pattern ≤ (2 : Int) + d95 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d111, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2857 pattern childGuard
    simpa only [d111, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d111, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2861 pattern childGuard
    simpa only [d111, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2863 (pattern : Ten) (guard : d451 pattern = 1) : d116 pattern ≤ (2 : Int) + d100 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d116, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2862 pattern childGuard
    simpa only [d116, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d116, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2854 pattern childGuard
    simpa only [d116, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2864 (pattern : Ten) (guard : d451 pattern = 1) : d119 pattern ≤ (2 : Int) + d470 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d119, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2855 pattern childGuard
    simpa only [d119, d470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d119, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2863 pattern childGuard
    simpa only [d119, d470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2865 (pattern : Ten) (guard : d451 pattern = 1) : d10 pattern ≤ (2 : Int) + d10 pattern := by
  omega
theorem c2866 (pattern : Ten) (guard : d451 pattern = 1) : d112 pattern ≤ (2 : Int) + d96 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d112, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d112, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d112, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2865 pattern childGuard
    simpa only [d112, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2867 (pattern : Ten) (guard : d451 pattern = 1) : d113 pattern ≤ (2 : Int) + d97 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d113, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d113, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d113, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2865 pattern childGuard
    simpa only [d113, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2868 (pattern : Ten) (guard : d451 pattern = 1) : d117 pattern ≤ (2 : Int) + d101 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d117, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2866 pattern childGuard
    simpa only [d117, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d117, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2867 pattern childGuard
    simpa only [d117, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2869 (pattern : Ten) (guard : d451 pattern = 1) : d114 pattern ≤ (2 : Int) + d98 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d114, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2861 pattern childGuard
    simpa only [d114, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d114, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2865 pattern childGuard
    simpa only [d114, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2870 (pattern : Ten) (guard : d451 pattern = 1) : d118 pattern ≤ (2 : Int) + d102 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d118, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2869 pattern childGuard
    simpa only [d118, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d118, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2867 pattern childGuard
    simpa only [d118, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2871 (pattern : Ten) (guard : d451 pattern = 1) : d120 pattern ≤ (2 : Int) + d104 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d120, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2868 pattern childGuard
    simpa only [d120, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d120, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2870 pattern childGuard
    simpa only [d120, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2872 (pattern : Ten) (guard : d451 pattern = 1) : d121 pattern ≤ (2 : Int) + d471 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d121, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2864 pattern childGuard
    simpa only [d121, d471, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d121, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2871 pattern childGuard
    simpa only [d121, d471, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2873 (pattern : Ten) (guard : d451 pattern = 1) : d122 pattern ≤ (2 : Int) + d106 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d122, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2871 pattern childGuard
    simpa only [d122, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d122, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2865 pattern childGuard
    simpa only [d122, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2874 (pattern : Ten) (guard : d451 pattern = 1) : d123 pattern ≤ (2 : Int) + d472 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d451 pattern = 1 := by simpa only [d123, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2872 pattern childGuard
    simpa only [d123, d472, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d451 pattern = 1 := by simpa only [d123, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d123, d472, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2875 (pattern : Ten) (guard : d0 pattern = 1) : d171 pattern ≤ (2 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2876 (pattern : Ten) (guard : d385 pattern = 1) : d174 pattern ≤ (2 : Int) + d171 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d385, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2875 pattern childGuard
    simpa only [d385, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d385, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2411 pattern childGuard
    simpa only [d385, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2877 (pattern : Ten) (guard : d460 pattern = 1) : d266 pattern ≤ (2 : Int) + d171 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d385 pattern = 1 := by simpa only [d460, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2876 pattern childGuard
    simpa only [d460, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d460, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2756 pattern childGuard
    simpa only [d460, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2878 (pattern : Ten) (guard : d0 pattern = 1) : d174 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2879 (pattern : Ten) (guard : d460 pattern = 1) : d174 pattern ≤ (2 : Int) + d250 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d385 pattern = 1 := by simpa only [d460, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2876 pattern childGuard
    simpa only [d460, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d460, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2878 pattern childGuard
    simpa only [d460, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
