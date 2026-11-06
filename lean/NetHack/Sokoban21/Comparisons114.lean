/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons113
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c15960 (pattern : Twelve) (guard : d2746 pattern = 1) : d6 pattern ≤ (1 : Int) + d6 pattern := by
  omega
theorem c15961 (pattern : Twelve) (guard : d2746 pattern = 1) : d503 pattern ≤ (1 : Int) + d2752 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d503, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15959 pattern childGuard
    simpa only [d503, d2752, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d503, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d503, d2752, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15962 (pattern : Twelve) (guard : d2746 pattern = 1) : d535 pattern ≤ (1 : Int) + d2753 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d535, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15956 pattern childGuard
    simpa only [d535, d2753, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d535, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15961 pattern childGuard
    simpa only [d535, d2753, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15963 (pattern : Twelve) (guard : d2746 pattern = 1) : d562 pattern ≤ (1 : Int) + d2754 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d562, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15952 pattern childGuard
    simpa only [d562, d2754, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d562, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15962 pattern childGuard
    simpa only [d562, d2754, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15964 (pattern : Twelve) (guard : d2746 pattern = 1) : d588 pattern ≤ (1 : Int) + d2755 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d588, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15947 pattern childGuard
    simpa only [d588, d2755, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d588, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15963 pattern childGuard
    simpa only [d588, d2755, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15965 (pattern : Twelve) (guard : d2746 pattern = 1) : d483 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15934 pattern childGuard
    simpa only [d2746, d483, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12247 pattern childGuard
    simpa only [d2746, d483, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15966 (pattern : Twelve) (guard : d7 pattern = 1) : d2 pattern ≤ (1 : Int) + d2 pattern := by
  omega
theorem c15967 (pattern : Twelve) (guard : d2746 pattern = 1) : d484 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15966 pattern childGuard
    simpa only [d2746, d484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12249 pattern childGuard
    simpa only [d2746, d484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15968 (pattern : Twelve) (guard : d2746 pattern = 1) : d504 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d504, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15965 pattern childGuard
    simpa only [d504, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d504, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15967 pattern childGuard
    simpa only [d504, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15969 (pattern : Twelve) (guard : d2746 pattern = 1) : d485 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15934 pattern childGuard
    simpa only [d2746, d485, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12252 pattern childGuard
    simpa only [d2746, d485, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15970 (pattern : Twelve) (guard : d0 pattern = 1) : d3 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15971 (pattern : Twelve) (guard : d7 pattern = 1) : d12 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15970 pattern childGuard
    simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11234 pattern childGuard
    simpa only [d7, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15972 (pattern : Twelve) (guard : d2746 pattern = 1) : d486 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15971 pattern childGuard
    simpa only [d2746, d486, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d2746, d486, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15973 (pattern : Twelve) (guard : d2746 pattern = 1) : d505 pattern ≤ (1 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d505, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15969 pattern childGuard
    simpa only [d505, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d505, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15972 pattern childGuard
    simpa only [d505, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15974 (pattern : Twelve) (guard : d2746 pattern = 1) : d536 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d536, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15968 pattern childGuard
    simpa only [d536, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d536, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15973 pattern childGuard
    simpa only [d536, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15975 (pattern : Twelve) (guard : d2746 pattern = 1) : d487 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15966 pattern childGuard
    simpa only [d2746, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11105 pattern childGuard
    simpa only [d2746, d487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15976 (pattern : Twelve) (guard : d2746 pattern = 1) : d506 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d506, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15969 pattern childGuard
    simpa only [d506, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d506, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15975 pattern childGuard
    simpa only [d506, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15977 (pattern : Twelve) (guard : d2746 pattern = 1) : d480 pattern ≤ (1 : Int) + d477 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d480, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15934 pattern childGuard
    simpa only [d2746, d480, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d480, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11094 pattern childGuard
    simpa only [d2746, d480, d477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15978 (pattern : Twelve) (guard : d0 pattern = 1) : d4 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15979 (pattern : Twelve) (guard : d7 pattern = 1) : d13 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15978 pattern childGuard
    simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15980 (pattern : Twelve) (guard : d2746 pattern = 1) : d170 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15979 pattern childGuard
    simpa only [d2746, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d2746, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15981 (pattern : Twelve) (guard : d2746 pattern = 1) : d507 pattern ≤ (1 : Int) + d2756 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d507, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d507, d2756, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d507, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15980 pattern childGuard
    simpa only [d507, d2756, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15982 (pattern : Twelve) (guard : d2746 pattern = 1) : d537 pattern ≤ (1 : Int) + d2757 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d537, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15976 pattern childGuard
    simpa only [d537, d2757, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d537, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15981 pattern childGuard
    simpa only [d537, d2757, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15983 (pattern : Twelve) (guard : d2746 pattern = 1) : d563 pattern ≤ (1 : Int) + d2758 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d563, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15974 pattern childGuard
    simpa only [d563, d2758, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d563, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15982 pattern childGuard
    simpa only [d563, d2758, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15984 (pattern : Twelve) (guard : d0 pattern = 1) : d5 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15985 (pattern : Twelve) (guard : d7 pattern = 1) : d14 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15984 pattern childGuard
    simpa only [d7, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11282 pattern childGuard
    simpa only [d7, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15986 (pattern : Twelve) (guard : d2746 pattern = 1) : d22 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15985 pattern childGuard
    simpa only [d2746, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d2746, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15987 (pattern : Twelve) (guard : d2746 pattern = 1) : d508 pattern ≤ (1 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d508, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d508, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d508, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15986 pattern childGuard
    simpa only [d508, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15988 (pattern : Twelve) (guard : d2746 pattern = 1) : d538 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d538, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15976 pattern childGuard
    simpa only [d538, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d538, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15987 pattern childGuard
    simpa only [d538, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15989 (pattern : Twelve) (guard : d2746 pattern = 1) : d487 pattern ≤ (1 : Int) + d2750 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d487, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15966 pattern childGuard
    simpa only [d2746, d487, d2750, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d487, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12318 pattern childGuard
    simpa only [d2746, d487, d2750, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15990 (pattern : Twelve) (guard : d2746 pattern = 1) : d509 pattern ≤ (1 : Int) + d2751 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d509, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d509, d2751, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d509, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15989 pattern childGuard
    simpa only [d509, d2751, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15991 (pattern : Twelve) (guard : d2746 pattern = 1) : d539 pattern ≤ (1 : Int) + d2753 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d539, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15990 pattern childGuard
    simpa only [d539, d2753, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d539, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15961 pattern childGuard
    simpa only [d539, d2753, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15992 (pattern : Twelve) (guard : d2746 pattern = 1) : d564 pattern ≤ (1 : Int) + d2759 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d564, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15988 pattern childGuard
    simpa only [d564, d2759, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d564, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15991 pattern childGuard
    simpa only [d564, d2759, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15993 (pattern : Twelve) (guard : d2746 pattern = 1) : d589 pattern ≤ (1 : Int) + d2760 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d589, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15983 pattern childGuard
    simpa only [d589, d2760, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d589, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15992 pattern childGuard
    simpa only [d589, d2760, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15994 (pattern : Twelve) (guard : d2746 pattern = 1) : d606 pattern ≤ (1 : Int) + d2761 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d606, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15964 pattern childGuard
    simpa only [d606, d2761, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d606, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15993 pattern childGuard
    simpa only [d606, d2761, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15995 (pattern : Twelve) (guard : d2746 pattern = 1) : d488 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15934 pattern childGuard
    simpa only [d2746, d488, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12278 pattern childGuard
    simpa only [d2746, d488, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15996 (pattern : Twelve) (guard : d2746 pattern = 1) : d510 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15965 pattern childGuard
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15995 pattern childGuard
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15997 (pattern : Twelve) (guard : d2746 pattern = 1) : d511 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15969 pattern childGuard
    simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15998 (pattern : Twelve) (guard : d2746 pattern = 1) : d540 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15996 pattern childGuard
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15997 pattern childGuard
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15999 (pattern : Twelve) (guard : d2746 pattern = 1) : d512 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d512, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15969 pattern childGuard
    simpa only [d512, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d512, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15944 pattern childGuard
    simpa only [d512, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16000 (pattern : Twelve) (guard : d2746 pattern = 1) : d513 pattern ≤ (1 : Int) + d2747 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d513, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d513, d2747, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d513, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15944 pattern childGuard
    simpa only [d513, d2747, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16001 (pattern : Twelve) (guard : d2746 pattern = 1) : d541 pattern ≤ (1 : Int) + d2748 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d541, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15999 pattern childGuard
    simpa only [d541, d2748, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d541, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16000 pattern childGuard
    simpa only [d541, d2748, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16002 (pattern : Twelve) (guard : d2746 pattern = 1) : d565 pattern ≤ (1 : Int) + d2749 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d565, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15998 pattern childGuard
    simpa only [d565, d2749, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d565, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16001 pattern childGuard
    simpa only [d565, d2749, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16003 (pattern : Twelve) (guard : d2746 pattern = 1) : d542 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15997 pattern childGuard
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16004 (pattern : Twelve) (guard : d2746 pattern = 1) : d566 pattern ≤ (1 : Int) + d2754 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d566, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16003 pattern childGuard
    simpa only [d566, d2754, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d566, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15991 pattern childGuard
    simpa only [d566, d2754, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16005 (pattern : Twelve) (guard : d2746 pattern = 1) : d590 pattern ≤ (1 : Int) + d2755 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d590, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16002 pattern childGuard
    simpa only [d590, d2755, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d590, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16004 pattern childGuard
    simpa only [d590, d2755, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16006 (pattern : Twelve) (guard : d2746 pattern = 1) : d489 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15934 pattern childGuard
    simpa only [d2746, d489, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12292 pattern childGuard
    simpa only [d2746, d489, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16007 (pattern : Twelve) (guard : d2746 pattern = 1) : d514 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d514, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16006 pattern childGuard
    simpa only [d514, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d514, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15975 pattern childGuard
    simpa only [d514, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16008 (pattern : Twelve) (guard : d2746 pattern = 1) : d515 pattern ≤ (1 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d515, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d515, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d515, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d515, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16009 (pattern : Twelve) (guard : d2746 pattern = 1) : d543 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d543, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16007 pattern childGuard
    simpa only [d543, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d543, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16008 pattern childGuard
    simpa only [d543, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16010 (pattern : Twelve) (guard : d2746 pattern = 1) : d509 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d509, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d509, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d509, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15975 pattern childGuard
    simpa only [d509, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16011 (pattern : Twelve) (guard : d2746 pattern = 1) : d515 pattern ≤ (1 : Int) + d2756 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d515, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d515, d2756, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d515, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d515, d2756, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16012 (pattern : Twelve) (guard : d2746 pattern = 1) : d544 pattern ≤ (1 : Int) + d2757 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d544, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16010 pattern childGuard
    simpa only [d544, d2757, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d544, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16011 pattern childGuard
    simpa only [d544, d2757, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16013 (pattern : Twelve) (guard : d2746 pattern = 1) : d567 pattern ≤ (1 : Int) + d2758 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d567, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16009 pattern childGuard
    simpa only [d567, d2758, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d567, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16012 pattern childGuard
    simpa only [d567, d2758, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16014 (pattern : Twelve) (guard : d2746 pattern = 1) : d544 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d544, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16010 pattern childGuard
    simpa only [d544, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d544, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16008 pattern childGuard
    simpa only [d544, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16015 (pattern : Twelve) (guard : d2746 pattern = 1) : d568 pattern ≤ (1 : Int) + d2759 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d568, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16014 pattern childGuard
    simpa only [d568, d2759, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d568, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15991 pattern childGuard
    simpa only [d568, d2759, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16016 (pattern : Twelve) (guard : d2746 pattern = 1) : d591 pattern ≤ (1 : Int) + d2760 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d591, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16013 pattern childGuard
    simpa only [d591, d2760, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d591, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16015 pattern childGuard
    simpa only [d591, d2760, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16017 (pattern : Twelve) (guard : d2746 pattern = 1) : d607 pattern ≤ (1 : Int) + d2761 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d607, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16005 pattern childGuard
    simpa only [d607, d2761, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d607, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16016 pattern childGuard
    simpa only [d607, d2761, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16018 (pattern : Twelve) (guard : d2746 pattern = 1) : d618 pattern ≤ (1 : Int) + d2761 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15994 pattern childGuard
    simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16017 pattern childGuard
    simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16019 (pattern : Twelve) (guard : d2746 pattern = 1) : d490 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15934 pattern childGuard
    simpa only [d2746, d490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12308 pattern childGuard
    simpa only [d2746, d490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16020 (pattern : Twelve) (guard : d2746 pattern = 1) : d491 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15966 pattern childGuard
    simpa only [d2746, d491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12310 pattern childGuard
    simpa only [d2746, d491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16021 (pattern : Twelve) (guard : d2746 pattern = 1) : d516 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d516, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16019 pattern childGuard
    simpa only [d516, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d516, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16020 pattern childGuard
    simpa only [d516, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16022 (pattern : Twelve) (guard : d2746 pattern = 1) : d517 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d517, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15995 pattern childGuard
    simpa only [d517, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d517, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15975 pattern childGuard
    simpa only [d517, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16023 (pattern : Twelve) (guard : d2746 pattern = 1) : d545 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16021 pattern childGuard
    simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16022 pattern childGuard
    simpa only [d545, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16024 (pattern : Twelve) (guard : d7 pattern = 1) : d3 pattern ≤ (1 : Int) + d3 pattern := by
  omega
theorem c16025 (pattern : Twelve) (guard : d2746 pattern = 1) : d492 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16024 pattern childGuard
    simpa only [d2746, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12318 pattern childGuard
    simpa only [d2746, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16026 (pattern : Twelve) (guard : d2746 pattern = 1) : d518 pattern ≤ (1 : Int) + d2762 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d518, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d518, d2762, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d518, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16025 pattern childGuard
    simpa only [d518, d2762, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16027 (pattern : Twelve) (guard : d2746 pattern = 1) : d546 pattern ≤ (1 : Int) + d2763 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d546, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16022 pattern childGuard
    simpa only [d546, d2763, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d546, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16026 pattern childGuard
    simpa only [d546, d2763, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16028 (pattern : Twelve) (guard : d2746 pattern = 1) : d569 pattern ≤ (1 : Int) + d2764 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d569, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16023 pattern childGuard
    simpa only [d569, d2764, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d569, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16027 pattern childGuard
    simpa only [d569, d2764, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16029 (pattern : Twelve) (guard : d2746 pattern = 1) : d547 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16022 pattern childGuard
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16010 pattern childGuard
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16030 (pattern : Twelve) (guard : d2746 pattern = 1) : d570 pattern ≤ (1 : Int) + d2765 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d570, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16029 pattern childGuard
    simpa only [d570, d2765, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d570, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15991 pattern childGuard
    simpa only [d570, d2765, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16031 (pattern : Twelve) (guard : d2746 pattern = 1) : d592 pattern ≤ (1 : Int) + d2766 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d592, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16028 pattern childGuard
    simpa only [d592, d2766, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d592, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16030 pattern childGuard
    simpa only [d592, d2766, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16032 (pattern : Twelve) (guard : d2746 pattern = 1) : d493 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15966 pattern childGuard
    simpa only [d2746, d493, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12326 pattern childGuard
    simpa only [d2746, d493, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16033 (pattern : Twelve) (guard : d7 pattern = 1) : d4 pattern ≤ (1 : Int) + d4 pattern := by
  omega
theorem c16034 (pattern : Twelve) (guard : d2746 pattern = 1) : d494 pattern ≤ (1 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16033 pattern childGuard
    simpa only [d2746, d494, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11128 pattern childGuard
    simpa only [d2746, d494, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16035 (pattern : Twelve) (guard : d2746 pattern = 1) : d519 pattern ≤ (1 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d519, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16032 pattern childGuard
    simpa only [d519, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d519, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16034 pattern childGuard
    simpa only [d519, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16036 (pattern : Twelve) (guard : d2746 pattern = 1) : d520 pattern ≤ (1 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d520, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15975 pattern childGuard
    simpa only [d520, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d520, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d520, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16037 (pattern : Twelve) (guard : d2746 pattern = 1) : d548 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d548, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16035 pattern childGuard
    simpa only [d548, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d548, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16036 pattern childGuard
    simpa only [d548, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16038 (pattern : Twelve) (guard : d2746 pattern = 1) : d521 pattern ≤ (1 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15975 pattern childGuard
    simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16034 pattern childGuard
    simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16039 (pattern : Twelve) (guard : d2746 pattern = 1) : d520 pattern ≤ (1 : Int) + d2752 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d520, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15989 pattern childGuard
    simpa only [d520, d2752, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d520, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d520, d2752, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16040 (pattern : Twelve) (guard : d2746 pattern = 1) : d549 pattern ≤ (1 : Int) + d2767 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d549, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16038 pattern childGuard
    simpa only [d549, d2767, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d549, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16039 pattern childGuard
    simpa only [d549, d2767, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16041 (pattern : Twelve) (guard : d2746 pattern = 1) : d571 pattern ≤ (1 : Int) + d2768 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d571, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16037 pattern childGuard
    simpa only [d571, d2768, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d571, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16040 pattern childGuard
    simpa only [d571, d2768, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16042 (pattern : Twelve) (guard : d2746 pattern = 1) : d549 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d549, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16038 pattern childGuard
    simpa only [d549, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d549, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16036 pattern childGuard
    simpa only [d549, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16043 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16044 (pattern : Twelve) (guard : d2746 pattern = 1) : d494 pattern ≤ (1 : Int) + d2769 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d494, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16033 pattern childGuard
    simpa only [d2746, d494, d2769, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d494, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16043 pattern childGuard
    simpa only [d2746, d494, d2769, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16045 (pattern : Twelve) (guard : d2746 pattern = 1) : d521 pattern ≤ (1 : Int) + d2770 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d521, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15989 pattern childGuard
    simpa only [d521, d2770, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d521, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16044 pattern childGuard
    simpa only [d521, d2770, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16046 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (1 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16047 (pattern : Twelve) (guard : d7 pattern = 1) : d16 pattern ≤ (1 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16046 pattern childGuard
    simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12142 pattern childGuard
    simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16048 (pattern : Twelve) (guard : d2746 pattern = 1) : d495 pattern ≤ (1 : Int) + d2769 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d495, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16047 pattern childGuard
    simpa only [d2746, d495, d2769, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d495, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16043 pattern childGuard
    simpa only [d2746, d495, d2769, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16049 (pattern : Twelve) (guard : d2746 pattern = 1) : d522 pattern ≤ (1 : Int) + d2771 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d522, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16048 pattern childGuard
    simpa only [d522, d2771, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d522, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d522, d2771, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16050 (pattern : Twelve) (guard : d2746 pattern = 1) : d550 pattern ≤ (1 : Int) + d2772 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d550, d2772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16045 pattern childGuard
    simpa only [d550, d2772, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d550, d2772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16049 pattern childGuard
    simpa only [d550, d2772, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16051 (pattern : Twelve) (guard : d2746 pattern = 1) : d572 pattern ≤ (1 : Int) + d2773 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d572, d2773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16042 pattern childGuard
    simpa only [d572, d2773, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d572, d2773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16050 pattern childGuard
    simpa only [d572, d2773, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16052 (pattern : Twelve) (guard : d2746 pattern = 1) : d593 pattern ≤ (1 : Int) + d2774 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d593, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16041 pattern childGuard
    simpa only [d593, d2774, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d593, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16051 pattern childGuard
    simpa only [d593, d2774, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16053 (pattern : Twelve) (guard : d2746 pattern = 1) : d608 pattern ≤ (1 : Int) + d2775 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d608, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16031 pattern childGuard
    simpa only [d608, d2775, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d608, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16052 pattern childGuard
    simpa only [d608, d2775, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16054 (pattern : Twelve) (guard : d2746 pattern = 1) : d496 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15934 pattern childGuard
    simpa only [d2746, d496, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12351 pattern childGuard
    simpa only [d2746, d496, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16055 (pattern : Twelve) (guard : d2746 pattern = 1) : d523 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d523, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16054 pattern childGuard
    simpa only [d523, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d523, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15975 pattern childGuard
    simpa only [d523, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16056 (pattern : Twelve) (guard : d2746 pattern = 1) : d551 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d551, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16055 pattern childGuard
    simpa only [d551, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d551, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16008 pattern childGuard
    simpa only [d551, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16057 (pattern : Twelve) (guard : d2746 pattern = 1) : d573 pattern ≤ (1 : Int) + d2758 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d573, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16056 pattern childGuard
    simpa only [d573, d2758, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d573, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16012 pattern childGuard
    simpa only [d573, d2758, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16058 (pattern : Twelve) (guard : d2746 pattern = 1) : d594 pattern ≤ (1 : Int) + d2760 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d594, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16057 pattern childGuard
    simpa only [d594, d2760, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d594, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16015 pattern childGuard
    simpa only [d594, d2760, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16059 (pattern : Twelve) (guard : d2746 pattern = 1) : d609 pattern ≤ (1 : Int) + d2776 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d609, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16058 pattern childGuard
    simpa only [d609, d2776, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d609, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d609, d2776, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16060 (pattern : Twelve) (guard : d2746 pattern = 1) : d619 pattern ≤ (1 : Int) + d2777 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d619, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16053 pattern childGuard
    simpa only [d619, d2777, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d619, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16059 pattern childGuard
    simpa only [d619, d2777, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16061 (pattern : Twelve) (guard : d2746 pattern = 1) : d624 pattern ≤ (1 : Int) + d2778 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d624, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16018 pattern childGuard
    simpa only [d624, d2778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d624, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16060 pattern childGuard
    simpa only [d624, d2778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16062 (pattern : Twelve) (guard : d2746 pattern = 1) : d513 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d513, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d513, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d513, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15944 pattern childGuard
    simpa only [d513, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16063 (pattern : Twelve) (guard : d2746 pattern = 1) : d513 pattern ≤ (1 : Int) + d2748 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16062 pattern childGuard
    simpa only [d2748, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16000 pattern childGuard
    simpa only [d2748, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16064 (pattern : Twelve) (guard : d2746 pattern = 1) : d574 pattern ≤ (1 : Int) + d2749 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d574, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d574, d2749, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d574, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16063 pattern childGuard
    simpa only [d574, d2749, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16065 (pattern : Twelve) (guard : d2746 pattern = 1) : d524 pattern ≤ (1 : Int) + d2751 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d524, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d524, d2751, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d524, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15955 pattern childGuard
    simpa only [d524, d2751, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16066 (pattern : Twelve) (guard : d2746 pattern = 1) : d552 pattern ≤ (1 : Int) + d2753 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d552, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16065 pattern childGuard
    simpa only [d552, d2753, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d552, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15961 pattern childGuard
    simpa only [d552, d2753, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16067 (pattern : Twelve) (guard : d2746 pattern = 1) : d575 pattern ≤ (1 : Int) + d2754 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d575, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d575, d2754, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d575, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16066 pattern childGuard
    simpa only [d575, d2754, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16068 (pattern : Twelve) (guard : d2746 pattern = 1) : d595 pattern ≤ (1 : Int) + d2755 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d595, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16064 pattern childGuard
    simpa only [d595, d2755, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d595, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16067 pattern childGuard
    simpa only [d595, d2755, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16069 (pattern : Twelve) (guard : d2746 pattern = 1) : d525 pattern ≤ (1 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d525, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d525, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d525, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15972 pattern childGuard
    simpa only [d525, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16070 (pattern : Twelve) (guard : d2746 pattern = 1) : d553 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d553, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16010 pattern childGuard
    simpa only [d553, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d553, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16069 pattern childGuard
    simpa only [d553, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16071 (pattern : Twelve) (guard : d2746 pattern = 1) : d554 pattern ≤ (1 : Int) + d2757 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d554, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16010 pattern childGuard
    simpa only [d554, d2757, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d554, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15981 pattern childGuard
    simpa only [d554, d2757, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16072 (pattern : Twelve) (guard : d2746 pattern = 1) : d576 pattern ≤ (1 : Int) + d2758 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d576, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16070 pattern childGuard
    simpa only [d576, d2758, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d576, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16071 pattern childGuard
    simpa only [d576, d2758, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16073 (pattern : Twelve) (guard : d2746 pattern = 1) : d555 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d555, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16010 pattern childGuard
    simpa only [d555, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d555, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15987 pattern childGuard
    simpa only [d555, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16074 (pattern : Twelve) (guard : d2746 pattern = 1) : d577 pattern ≤ (1 : Int) + d2759 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d577, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16073 pattern childGuard
    simpa only [d577, d2759, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d577, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15991 pattern childGuard
    simpa only [d577, d2759, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16075 (pattern : Twelve) (guard : d2746 pattern = 1) : d596 pattern ≤ (1 : Int) + d2760 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d596, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16072 pattern childGuard
    simpa only [d596, d2760, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d596, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16074 pattern childGuard
    simpa only [d596, d2760, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16076 (pattern : Twelve) (guard : d2746 pattern = 1) : d610 pattern ≤ (1 : Int) + d2761 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d610, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16068 pattern childGuard
    simpa only [d610, d2761, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d610, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16075 pattern childGuard
    simpa only [d610, d2761, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16077 (pattern : Twelve) (guard : d2746 pattern = 1) : d578 pattern ≤ (1 : Int) + d2754 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d578, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d578, d2754, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d578, d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15991 pattern childGuard
    simpa only [d578, d2754, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16078 (pattern : Twelve) (guard : d2746 pattern = 1) : d597 pattern ≤ (1 : Int) + d2755 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d597, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16064 pattern childGuard
    simpa only [d597, d2755, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d597, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16077 pattern childGuard
    simpa only [d597, d2755, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16079 (pattern : Twelve) (guard : d2746 pattern = 1) : d544 pattern ≤ (1 : Int) + d2758 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16014 pattern childGuard
    simpa only [d2758, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16012 pattern childGuard
    simpa only [d2758, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16080 (pattern : Twelve) (guard : d2746 pattern = 1) : d598 pattern ≤ (1 : Int) + d2760 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d598, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16079 pattern childGuard
    simpa only [d598, d2760, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d598, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16015 pattern childGuard
    simpa only [d598, d2760, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16081 (pattern : Twelve) (guard : d2746 pattern = 1) : d611 pattern ≤ (1 : Int) + d2761 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d611, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16078 pattern childGuard
    simpa only [d611, d2761, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d611, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16080 pattern childGuard
    simpa only [d611, d2761, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16082 (pattern : Twelve) (guard : d2746 pattern = 1) : d620 pattern ≤ (1 : Int) + d2761 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16076 pattern childGuard
    simpa only [d620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16081 pattern childGuard
    simpa only [d620, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16083 (pattern : Twelve) (guard : d2746 pattern = 1) : d556 pattern ≤ (1 : Int) + d2763 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d556, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16010 pattern childGuard
    simpa only [d556, d2763, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d556, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16026 pattern childGuard
    simpa only [d556, d2763, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16084 (pattern : Twelve) (guard : d2746 pattern = 1) : d579 pattern ≤ (1 : Int) + d2764 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d579, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16010 pattern childGuard
    simpa only [d579, d2764, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d579, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16083 pattern childGuard
    simpa only [d579, d2764, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16085 (pattern : Twelve) (guard : d2746 pattern = 1) : d580 pattern ≤ (1 : Int) + d2765 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d580, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16010 pattern childGuard
    simpa only [d580, d2765, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d580, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15991 pattern childGuard
    simpa only [d580, d2765, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16086 (pattern : Twelve) (guard : d2746 pattern = 1) : d599 pattern ≤ (1 : Int) + d2766 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d599, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16084 pattern childGuard
    simpa only [d599, d2766, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d599, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16085 pattern childGuard
    simpa only [d599, d2766, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16087 (pattern : Twelve) (guard : d2746 pattern = 1) : d549 pattern ≤ (1 : Int) + d2768 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16042 pattern childGuard
    simpa only [d2768, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16040 pattern childGuard
    simpa only [d2768, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16088 (pattern : Twelve) (guard : d2746 pattern = 1) : d600 pattern ≤ (1 : Int) + d2774 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d600, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16087 pattern childGuard
    simpa only [d600, d2774, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d600, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16051 pattern childGuard
    simpa only [d600, d2774, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16089 (pattern : Twelve) (guard : d2746 pattern = 1) : d612 pattern ≤ (1 : Int) + d2775 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d612, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16086 pattern childGuard
    simpa only [d612, d2775, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d612, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16088 pattern childGuard
    simpa only [d612, d2775, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16090 (pattern : Twelve) (guard : d2746 pattern = 1) : d613 pattern ≤ (1 : Int) + d2776 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d613, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16080 pattern childGuard
    simpa only [d613, d2776, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d613, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d613, d2776, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16091 (pattern : Twelve) (guard : d2746 pattern = 1) : d621 pattern ≤ (1 : Int) + d2777 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d621, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16089 pattern childGuard
    simpa only [d621, d2777, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d621, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16090 pattern childGuard
    simpa only [d621, d2777, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16092 (pattern : Twelve) (guard : d2746 pattern = 1) : d625 pattern ≤ (1 : Int) + d2778 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d625, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16082 pattern childGuard
    simpa only [d625, d2778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d625, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16091 pattern childGuard
    simpa only [d625, d2778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16093 (pattern : Twelve) (guard : d2746 pattern = 1) : d627 pattern ≤ (1 : Int) + d2778 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16061 pattern childGuard
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16092 pattern childGuard
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16094 (pattern : Twelve) (guard : d2746 pattern = 1) : d628 pattern ≤ (1 : Int) + d2778 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16093 pattern childGuard
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16092 pattern childGuard
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16095 (pattern : Twelve) (guard : d2746 pattern = 1) : d526 pattern ≤ (1 : Int) + d2779 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d526, d2779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d526, d2779, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d526, d2779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16048 pattern childGuard
    simpa only [d526, d2779, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16096 (pattern : Twelve) (guard : d2746 pattern = 1) : d557 pattern ≤ (1 : Int) + d2780 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d557, d2780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16095 pattern childGuard
    simpa only [d557, d2780, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d557, d2780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15961 pattern childGuard
    simpa only [d557, d2780, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16097 (pattern : Twelve) (guard : d2746 pattern = 1) : d581 pattern ≤ (1 : Int) + d2781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d581, d2781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d581, d2781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d581, d2781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16096 pattern childGuard
    simpa only [d581, d2781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16098 (pattern : Twelve) (guard : d2746 pattern = 1) : d601 pattern ≤ (1 : Int) + d2782 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d601, d2782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16064 pattern childGuard
    simpa only [d601, d2782, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d601, d2782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16097 pattern childGuard
    simpa only [d601, d2782, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16099 (pattern : Twelve) (guard : d2746 pattern = 1) : d509 pattern ≤ (1 : Int) + d2783 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d509, d2783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d509, d2783, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d509, d2783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15989 pattern childGuard
    simpa only [d509, d2783, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
