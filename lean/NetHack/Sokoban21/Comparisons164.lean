/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons163
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c22960 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (20 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22958 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22959 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22961 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (20 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22958 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22960 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22962 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (20 : Int) + d1 pattern := by
  omega
theorem c22963 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (20 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22961 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22962 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22964 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (20 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22959 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22962 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22965 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (20 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22960 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22964 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22966 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (20 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22965 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22962 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22967 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (20 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22963 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22966 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22968 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (20 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22958 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22967 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22969 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (20 : Int) + d2 pattern := by
  change (0 : Int) ≤ (20 : Int) + 2
  decide
theorem c22970 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (20 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22958 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22969 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22971 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (20 : Int) + d3 pattern := by
  change (1 : Int) ≤ (20 : Int) + 3
  decide
theorem c22972 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (20 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22959 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22971 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22973 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (20 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22970 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22972 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22974 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (20 : Int) + d2 pattern := by
  change (1 : Int) ≤ (20 : Int) + 2
  decide
theorem c22975 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (20 : Int) + d4 pattern := by
  change (2 : Int) ≤ (20 : Int) + 4
  decide
theorem c22976 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (20 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22974 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22975 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22977 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (20 : Int) + d3 pattern := by
  change (2 : Int) ≤ (20 : Int) + 3
  decide
theorem c22978 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (20 : Int) + d5 pattern := by
  change (3 : Int) ≤ (20 : Int) + 5
  decide
theorem c22979 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (20 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22977 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22978 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22980 (pattern : Twelve) (guard : d1 pattern = 1) : d18 pattern ≤ (20 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22976 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22979 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22981 (pattern : Twelve) (guard : d1 pattern = 1) : d28 pattern ≤ (20 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22973 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22980 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22982 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (20 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22969 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22975 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22983 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (20 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22971 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22978 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22984 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (20 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22982 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22983 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22985 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (20 : Int) + d6 pattern := by
  omega
theorem c22986 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (20 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22984 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22987 (pattern : Twelve) (guard : d1 pattern = 1) : d51 pattern ≤ (20 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22981 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22986 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22988 (pattern : Twelve) (guard : d1 pattern = 1) : d73 pattern ≤ (20 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22961 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22987 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22989 (pattern : Twelve) (guard : d1 pattern = 1) : d91 pattern ≤ (20 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22968 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22988 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22990 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (20 : Int) + d30 pattern := by
  omega
theorem c22991 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (20 : Int) + d6 pattern := by
  change (3 : Int) ≤ (20 : Int) + 6
  decide
theorem c22992 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (20 : Int) + d6 pattern := by
  change (5 : Int) ≤ (20 : Int) + 6
  decide
theorem c22993 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22991 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22992 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22994 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (20 : Int) + d6 pattern := by
  change (4 : Int) ≤ (20 : Int) + 6
  decide
theorem c22995 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22994 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22996 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22993 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22995 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22997 (pattern : Twelve) (guard : d1 pattern = 1) : d31 pattern ≤ (20 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22958 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22996 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22998 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (20 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22990 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22997 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22999 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (20 : Int) + d2 pattern := by
  omega
theorem c23000 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (20 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22999 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22977 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23001 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (20 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22999 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23000 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23002 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (20 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22961 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23001 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23003 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22992 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23004 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22995 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23003 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23005 (pattern : Twelve) (guard : d1 pattern = 1) : d32 pattern ≤ (20 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22965 pattern childGuard
    simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23004 pattern childGuard
    simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23006 (pattern : Twelve) (guard : d1 pattern = 1) : d53 pattern ≤ (20 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23005 pattern childGuard
    simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23007 (pattern : Twelve) (guard : d1 pattern = 1) : d74 pattern ≤ (20 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22998 pattern childGuard
    simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23006 pattern childGuard
    simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23008 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23003 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23009 (pattern : Twelve) (guard : d1 pattern = 1) : d33 pattern ≤ (20 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22961 pattern childGuard
    simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23008 pattern childGuard
    simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23010 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (20 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23009 pattern childGuard
    simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23011 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (20 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22999 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22975 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23012 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (20 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23011 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22979 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23013 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (20 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22973 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23012 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23014 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (20 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23013 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22986 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23015 (pattern : Twelve) (guard : d1 pattern = 1) : d75 pattern ≤ (20 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23010 pattern childGuard
    simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23014 pattern childGuard
    simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23016 (pattern : Twelve) (guard : d1 pattern = 1) : d92 pattern ≤ (20 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23007 pattern childGuard
    simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23015 pattern childGuard
    simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23017 (pattern : Twelve) (guard : d1 pattern = 1) : d102 pattern ≤ (20 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22989 pattern childGuard
    simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23016 pattern childGuard
    simpa only [d102, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23018 (pattern : Twelve) (guard : d1 pattern = 1) : d76 pattern ≤ (20 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22961 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23014 pattern childGuard
    simpa only [d76, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23019 (pattern : Twelve) (guard : d1 pattern = 1) : d93 pattern ≤ (20 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22968 pattern childGuard
    simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23018 pattern childGuard
    simpa only [d93, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23020 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (20 : Int) + d56 pattern := by
  omega
theorem c23021 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (20 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22965 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d36, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23022 (pattern : Twelve) (guard : d1 pattern = 1) : d57 pattern ≤ (20 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23021 pattern childGuard
    simpa only [d57, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23023 (pattern : Twelve) (guard : d1 pattern = 1) : d77 pattern ≤ (20 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23020 pattern childGuard
    simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23022 pattern childGuard
    simpa only [d77, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23024 (pattern : Twelve) (guard : d1 pattern = 1) : d35 pattern ≤ (20 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22961 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d35, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23025 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (20 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23024 pattern childGuard
    simpa only [d56, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23026 (pattern : Twelve) (guard : d1 pattern = 1) : d78 pattern ≤ (20 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23025 pattern childGuard
    simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23014 pattern childGuard
    simpa only [d78, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23027 (pattern : Twelve) (guard : d1 pattern = 1) : d94 pattern ≤ (20 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23023 pattern childGuard
    simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23026 pattern childGuard
    simpa only [d94, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23028 (pattern : Twelve) (guard : d1 pattern = 1) : d103 pattern ≤ (20 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23019 pattern childGuard
    simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23027 pattern childGuard
    simpa only [d103, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23029 (pattern : Twelve) (guard : d1 pattern = 1) : d110 pattern ≤ (20 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23017 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23028 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23030 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (20 : Int) + d3 pattern := by
  omega
theorem c23031 (pattern : Twelve) (guard : d1 pattern = 1) : d37 pattern ≤ (20 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22965 pattern childGuard
    simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23030 pattern childGuard
    simpa only [d37, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23032 (pattern : Twelve) (guard : d1 pattern = 1) : d58 pattern ≤ (20 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23031 pattern childGuard
    simpa only [d58, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23033 (pattern : Twelve) (guard : d1 pattern = 1) : d79 pattern ≤ (20 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22990 pattern childGuard
    simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23032 pattern childGuard
    simpa only [d79, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23034 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (20 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23014 pattern childGuard
    simpa only [d80, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23035 (pattern : Twelve) (guard : d1 pattern = 1) : d95 pattern ≤ (20 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23033 pattern childGuard
    simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23034 pattern childGuard
    simpa only [d95, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23036 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (20 : Int) + d59 pattern := by
  omega
theorem c23037 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (20 : Int) + d4 pattern := by
  omega
theorem c23038 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (20 : Int) + d5 pattern := by
  change (4 : Int) ≤ (20 : Int) + 5
  decide
theorem c23039 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (20 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23037 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23038 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23040 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (20 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23037 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23039 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23041 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (20 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23001 pattern childGuard
    simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23040 pattern childGuard
    simpa only [d38, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23042 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (20 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22977 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23030 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23043 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (20 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23000 pattern childGuard
    simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23042 pattern childGuard
    simpa only [d23, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23044 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (20 : Int) + d820 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23043 pattern childGuard
    simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d40, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23045 (pattern : Twelve) (guard : d1 pattern = 1) : d60 pattern ≤ (20 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23041 pattern childGuard
    simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23044 pattern childGuard
    simpa only [d60, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23046 (pattern : Twelve) (guard : d1 pattern = 1) : d81 pattern ≤ (20 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23036 pattern childGuard
    simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23045 pattern childGuard
    simpa only [d81, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23047 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (20 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23001 pattern childGuard
    simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d39, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23048 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (20 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23041 pattern childGuard
    simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23047 pattern childGuard
    simpa only [d59, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23049 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (20 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23037 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22994 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23050 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (20 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23038 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22992 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23051 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (20 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23049 pattern childGuard
    simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23050 pattern childGuard
    simpa only [d24, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23052 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (20 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23012 pattern childGuard
    simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23051 pattern childGuard
    simpa only [d41, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23053 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (20 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22975 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22994 pattern childGuard
    simpa only [d16, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23054 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (20 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22978 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22992 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23055 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (20 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23053 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23054 pattern childGuard
    simpa only [d25, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23056 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (20 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23055 pattern childGuard
    simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d42, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23057 (pattern : Twelve) (guard : d1 pattern = 1) : d61 pattern ≤ (20 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23052 pattern childGuard
    simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23056 pattern childGuard
    simpa only [d61, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23058 (pattern : Twelve) (guard : d1 pattern = 1) : d82 pattern ≤ (20 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23048 pattern childGuard
    simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23057 pattern childGuard
    simpa only [d82, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23059 (pattern : Twelve) (guard : d1 pattern = 1) : d96 pattern ≤ (20 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23046 pattern childGuard
    simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23058 pattern childGuard
    simpa only [d96, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23060 (pattern : Twelve) (guard : d1 pattern = 1) : d104 pattern ≤ (20 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23035 pattern childGuard
    simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23059 pattern childGuard
    simpa only [d104, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23061 (pattern : Twelve) (guard : d1 pattern = 1) : d105 pattern ≤ (20 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23027 pattern childGuard
    simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d105, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23062 (pattern : Twelve) (guard : d1 pattern = 1) : d111 pattern ≤ (20 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23060 pattern childGuard
    simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23061 pattern childGuard
    simpa only [d111, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23063 (pattern : Twelve) (guard : d1 pattern = 1) : d114 pattern ≤ (20 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23029 pattern childGuard
    simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23062 pattern childGuard
    simpa only [d114, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23064 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (20 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22961 pattern childGuard
    simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22999 pattern childGuard
    simpa only [d30, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23065 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (20 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23064 pattern childGuard
    simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23014 pattern childGuard
    simpa only [d80, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23066 (pattern : Twelve) (guard : d1 pattern = 1) : d97 pattern ≤ (20 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22968 pattern childGuard
    simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23065 pattern childGuard
    simpa only [d97, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23067 (pattern : Twelve) (guard : d1 pattern = 1) : d43 pattern ≤ (20 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22962 pattern childGuard
    simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23004 pattern childGuard
    simpa only [d43, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23068 (pattern : Twelve) (guard : d1 pattern = 1) : d62 pattern ≤ (20 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23067 pattern childGuard
    simpa only [d62, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23069 (pattern : Twelve) (guard : d1 pattern = 1) : d83 pattern ≤ (20 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22998 pattern childGuard
    simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23068 pattern childGuard
    simpa only [d83, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23070 (pattern : Twelve) (guard : d1 pattern = 1) : d44 pattern ≤ (20 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22999 pattern childGuard
    simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23008 pattern childGuard
    simpa only [d44, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23071 (pattern : Twelve) (guard : d1 pattern = 1) : d63 pattern ≤ (20 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23070 pattern childGuard
    simpa only [d63, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23072 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (20 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23012 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d40, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23073 (pattern : Twelve) (guard : d1 pattern = 1) : d64 pattern ≤ (20 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23013 pattern childGuard
    simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23072 pattern childGuard
    simpa only [d64, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23074 (pattern : Twelve) (guard : d1 pattern = 1) : d84 pattern ≤ (20 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23071 pattern childGuard
    simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23073 pattern childGuard
    simpa only [d84, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23075 (pattern : Twelve) (guard : d1 pattern = 1) : d98 pattern ≤ (20 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23069 pattern childGuard
    simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23074 pattern childGuard
    simpa only [d98, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23076 (pattern : Twelve) (guard : d1 pattern = 1) : d106 pattern ≤ (20 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23066 pattern childGuard
    simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23075 pattern childGuard
    simpa only [d106, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23077 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (20 : Int) + d45 pattern := by
  omega
theorem c23078 (pattern : Twelve) (guard : d1 pattern = 1) : d65 pattern ≤ (20 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23077 pattern childGuard
    simpa only [d65, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23079 (pattern : Twelve) (guard : d1 pattern = 1) : d85 pattern ≤ (20 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23020 pattern childGuard
    simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23078 pattern childGuard
    simpa only [d85, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23080 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (20 : Int) + d39 pattern := by
  omega
theorem c23081 (pattern : Twelve) (guard : d1 pattern = 1) : d66 pattern ≤ (20 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23080 pattern childGuard
    simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23082 (pattern : Twelve) (guard : d1 pattern = 1) : d86 pattern ≤ (20 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23081 pattern childGuard
    simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23073 pattern childGuard
    simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23083 (pattern : Twelve) (guard : d1 pattern = 1) : d99 pattern ≤ (20 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23079 pattern childGuard
    simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23082 pattern childGuard
    simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23084 (pattern : Twelve) (guard : d1 pattern = 1) : d107 pattern ≤ (20 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23066 pattern childGuard
    simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23083 pattern childGuard
    simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23085 (pattern : Twelve) (guard : d1 pattern = 1) : d112 pattern ≤ (20 : Int) + d864 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23076 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23084 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23086 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (20 : Int) + d46 pattern := by
  omega
theorem c23087 (pattern : Twelve) (guard : d1 pattern = 1) : d67 pattern ≤ (20 : Int) + d834 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23086 pattern childGuard
    simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23088 (pattern : Twelve) (guard : d1 pattern = 1) : d87 pattern ≤ (20 : Int) + d849 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22990 pattern childGuard
    simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23087 pattern childGuard
    simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23089 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (20 : Int) + d38 pattern := by
  omega
theorem c23090 (pattern : Twelve) (guard : d1 pattern = 1) : d68 pattern ≤ (20 : Int) + d835 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23089 pattern childGuard
    simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23091 (pattern : Twelve) (guard : d1 pattern = 1) : d88 pattern ≤ (20 : Int) + d850 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23090 pattern childGuard
    simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23073 pattern childGuard
    simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23092 (pattern : Twelve) (guard : d1 pattern = 1) : d100 pattern ≤ (20 : Int) + d859 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23088 pattern childGuard
    simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23091 pattern childGuard
    simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23093 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (20 : Int) + d47 pattern := by
  omega
theorem c23094 (pattern : Twelve) (guard : d1 pattern = 1) : d69 pattern ≤ (20 : Int) + d836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23041 pattern childGuard
    simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23093 pattern childGuard
    simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23095 (pattern : Twelve) (guard : d1 pattern = 1) : d89 pattern ≤ (20 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23036 pattern childGuard
    simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23094 pattern childGuard
    simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23096 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (20 : Int) + d48 pattern := by
  omega
theorem c23097 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (20 : Int) + d837 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23041 pattern childGuard
    simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23096 pattern childGuard
    simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23098 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (20 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23051 pattern childGuard
    simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23099 (pattern : Twelve) (guard : d1 pattern = 1) : d71 pattern ≤ (20 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23052 pattern childGuard
    simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23098 pattern childGuard
    simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
