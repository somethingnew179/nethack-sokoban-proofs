/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons106
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c14980 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2357 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14981 (pattern : Twelve) (guard : d2355 pattern = 1) : d438 pattern ≤ (0 : Int) + d2416 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d438, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14945 pattern childGuard
    simpa only [d2355, d438, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d438, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14980 pattern childGuard
    simpa only [d2355, d438, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14982 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2358 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14983 (pattern : Twelve) (guard : d2355 pattern = 1) : d438 pattern ≤ (0 : Int) + d2417 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d438, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14945 pattern childGuard
    simpa only [d2355, d438, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d438, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14982 pattern childGuard
    simpa only [d2355, d438, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14984 (pattern : Twelve) (guard : d2355 pattern = 1) : d438 pattern ≤ (0 : Int) + d2418 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14981 pattern childGuard
    simpa only [d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14983 pattern childGuard
    simpa only [d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14985 (pattern : Twelve) (guard : d0 pattern = 1) : d451 pattern ≤ (0 : Int) + d2418 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14986 (pattern : Twelve) (guard : d2356 pattern = 1) : d459 pattern ≤ (0 : Int) + d2418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14984 pattern childGuard
    simpa only [d2356, d459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14985 pattern childGuard
    simpa only [d2356, d459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14987 (pattern : Twelve) (guard : d0 pattern = 1) : d432 pattern ≤ (0 : Int) + d2418 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14988 (pattern : Twelve) (guard : d2356 pattern = 1) : d460 pattern ≤ (0 : Int) + d2418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14984 pattern childGuard
    simpa only [d2356, d460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14987 pattern childGuard
    simpa only [d2356, d460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14989 (pattern : Twelve) (guard : d2356 pattern = 1) : d467 pattern ≤ (0 : Int) + d2418 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14986 pattern childGuard
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14988 pattern childGuard
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14990 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2360 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14991 (pattern : Twelve) (guard : d2355 pattern = 1) : d441 pattern ≤ (0 : Int) + d2419 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d441, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14961 pattern childGuard
    simpa only [d2355, d441, d2419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d441, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14990 pattern childGuard
    simpa only [d2355, d441, d2419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14992 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2361 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14993 (pattern : Twelve) (guard : d2355 pattern = 1) : d441 pattern ≤ (0 : Int) + d2420 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d441, d2420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14961 pattern childGuard
    simpa only [d2355, d441, d2420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d441, d2420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14992 pattern childGuard
    simpa only [d2355, d441, d2420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14994 (pattern : Twelve) (guard : d2355 pattern = 1) : d441 pattern ≤ (0 : Int) + d2421 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14991 pattern childGuard
    simpa only [d2421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14993 pattern childGuard
    simpa only [d2421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14995 (pattern : Twelve) (guard : d0 pattern = 1) : d436 pattern ≤ (0 : Int) + d2421 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14996 (pattern : Twelve) (guard : d2356 pattern = 1) : d461 pattern ≤ (0 : Int) + d2421 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14994 pattern childGuard
    simpa only [d2356, d461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14995 pattern childGuard
    simpa only [d2356, d461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14997 (pattern : Twelve) (guard : d2356 pattern = 1) : d462 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14975 pattern childGuard
    simpa only [d2356, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d2356, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14998 (pattern : Twelve) (guard : d2356 pattern = 1) : d468 pattern ≤ (0 : Int) + d2476 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d468, d2476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14996 pattern childGuard
    simpa only [d468, d2476, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d468, d2476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14997 pattern childGuard
    simpa only [d468, d2476, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14999 (pattern : Twelve) (guard : d2356 pattern = 1) : d472 pattern ≤ (0 : Int) + d2477 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d472, d2477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14989 pattern childGuard
    simpa only [d472, d2477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d472, d2477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14998 pattern childGuard
    simpa only [d472, d2477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15000 (pattern : Twelve) (guard : d2356 pattern = 1) : d474 pattern ≤ (0 : Int) + d2477 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14979 pattern childGuard
    simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14999 pattern childGuard
    simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15001 (pattern : Twelve) (guard : d2356 pattern = 1) : d475 pattern ≤ (0 : Int) + d2477 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15000 pattern childGuard
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14999 pattern childGuard
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15002 (pattern : Twelve) (guard : d0 pattern = 1) : d452 pattern ≤ (0 : Int) + d2418 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15003 (pattern : Twelve) (guard : d2356 pattern = 1) : d463 pattern ≤ (0 : Int) + d2418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14984 pattern childGuard
    simpa only [d2356, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15002 pattern childGuard
    simpa only [d2356, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15004 (pattern : Twelve) (guard : d2356 pattern = 1) : d469 pattern ≤ (0 : Int) + d2418 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15003 pattern childGuard
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14988 pattern childGuard
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15005 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2367 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15006 (pattern : Twelve) (guard : d2355 pattern = 1) : d441 pattern ≤ (0 : Int) + d2426 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d441, d2426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14961 pattern childGuard
    simpa only [d2355, d441, d2426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d441, d2426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15005 pattern childGuard
    simpa only [d2355, d441, d2426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15007 (pattern : Twelve) (guard : d26 pattern = 1) : d123 pattern ≤ (0 : Int) + d3 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2915 pattern childGuard
    simpa only [d26, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d26, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15008 (pattern : Twelve) (guard : d26 pattern = 1) : d132 pattern ≤ (0 : Int) + d2427 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d132, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14961 pattern childGuard
    simpa only [d132, d2427, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d26 pattern = 1 := by simpa only [d132, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15007 pattern childGuard
    simpa only [d132, d2427, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15009 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2368 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15010 (pattern : Twelve) (guard : d2355 pattern = 1) : d442 pattern ≤ (0 : Int) + d2428 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d442, d2428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15008 pattern childGuard
    simpa only [d2355, d442, d2428, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d442, d2428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15009 pattern childGuard
    simpa only [d2355, d442, d2428, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15011 (pattern : Twelve) (guard : d2355 pattern = 1) : d453 pattern ≤ (0 : Int) + d2429 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d453, d2429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15006 pattern childGuard
    simpa only [d453, d2429, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d453, d2429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15010 pattern childGuard
    simpa only [d453, d2429, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15012 (pattern : Twelve) (guard : d0 pattern = 1) : d454 pattern ≤ (0 : Int) + d2429 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15013 (pattern : Twelve) (guard : d2356 pattern = 1) : d464 pattern ≤ (0 : Int) + d2429 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15011 pattern childGuard
    simpa only [d2356, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15012 pattern childGuard
    simpa only [d2356, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15014 (pattern : Twelve) (guard : d2356 pattern = 1) : d470 pattern ≤ (0 : Int) + d2478 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d470, d2478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15013 pattern childGuard
    simpa only [d470, d2478, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d470, d2478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14997 pattern childGuard
    simpa only [d470, d2478, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15015 (pattern : Twelve) (guard : d2356 pattern = 1) : d473 pattern ≤ (0 : Int) + d2479 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d473, d2479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15004 pattern childGuard
    simpa only [d473, d2479, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d473, d2479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15014 pattern childGuard
    simpa only [d473, d2479, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15016 (pattern : Twelve) (guard : d2356 pattern = 1) : d476 pattern ≤ (0 : Int) + d2480 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d476, d2480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15001 pattern childGuard
    simpa only [d476, d2480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d476, d2480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15015 pattern childGuard
    simpa only [d476, d2480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15017 (pattern : Twelve) (guard : d0 pattern = 1) : d186 pattern ≤ (0 : Int) + d2374 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15018 (pattern : Twelve) (guard : d2355 pattern = 1) : d426 pattern ≤ (0 : Int) + d2434 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d426, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14945 pattern childGuard
    simpa only [d2355, d426, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d426, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15017 pattern childGuard
    simpa only [d2355, d426, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15019 (pattern : Twelve) (guard : d26 pattern = 1) : d17 pattern ≤ (0 : Int) + d17 pattern := by
  omega
theorem c15020 (pattern : Twelve) (guard : d0 pattern = 1) : d908 pattern ≤ (0 : Int) + d2375 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15021 (pattern : Twelve) (guard : d2355 pattern = 1) : d1070 pattern ≤ (0 : Int) + d2435 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1070, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15019 pattern childGuard
    simpa only [d2355, d1070, d2435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1070, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15020 pattern childGuard
    simpa only [d2355, d1070, d2435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15022 (pattern : Twelve) (guard : d2355 pattern = 1) : d1078 pattern ≤ (0 : Int) + d2436 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1078, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15018 pattern childGuard
    simpa only [d1078, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1078, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15021 pattern childGuard
    simpa only [d1078, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15023 (pattern : Twelve) (guard : d0 pattern = 1) : d1079 pattern ≤ (0 : Int) + d2436 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15024 (pattern : Twelve) (guard : d2356 pattern = 1) : d1088 pattern ≤ (0 : Int) + d2436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15022 pattern childGuard
    simpa only [d2356, d1088, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15023 pattern childGuard
    simpa only [d2356, d1088, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15025 (pattern : Twelve) (guard : d0 pattern = 1) : d189 pattern ≤ (0 : Int) + d2374 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15026 (pattern : Twelve) (guard : d2355 pattern = 1) : d430 pattern ≤ (0 : Int) + d2434 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d430, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14945 pattern childGuard
    simpa only [d2355, d430, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d430, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15025 pattern childGuard
    simpa only [d2355, d430, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15027 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2375 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15028 (pattern : Twelve) (guard : d2355 pattern = 1) : d1073 pattern ≤ (0 : Int) + d2435 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1073, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15019 pattern childGuard
    simpa only [d2355, d1073, d2435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1073, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15027 pattern childGuard
    simpa only [d2355, d1073, d2435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15029 (pattern : Twelve) (guard : d2355 pattern = 1) : d1080 pattern ≤ (0 : Int) + d2436 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1080, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15026 pattern childGuard
    simpa only [d1080, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1080, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15028 pattern childGuard
    simpa only [d1080, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15030 (pattern : Twelve) (guard : d0 pattern = 1) : d1081 pattern ≤ (0 : Int) + d2436 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15031 (pattern : Twelve) (guard : d2356 pattern = 1) : d1089 pattern ≤ (0 : Int) + d2436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15029 pattern childGuard
    simpa only [d2356, d1089, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15030 pattern childGuard
    simpa only [d2356, d1089, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15032 (pattern : Twelve) (guard : d2356 pattern = 1) : d1095 pattern ≤ (0 : Int) + d2436 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15024 pattern childGuard
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15031 pattern childGuard
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15033 (pattern : Twelve) (guard : d0 pattern = 1) : d194 pattern ≤ (0 : Int) + d2377 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15034 (pattern : Twelve) (guard : d2355 pattern = 1) : d434 pattern ≤ (0 : Int) + d2437 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d434, d2437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14961 pattern childGuard
    simpa only [d2355, d434, d2437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d434, d2437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15033 pattern childGuard
    simpa only [d2355, d434, d2437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15035 (pattern : Twelve) (guard : d26 pattern = 1) : d34 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4484 pattern childGuard
    simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1340 pattern childGuard
    simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15036 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2378 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15037 (pattern : Twelve) (guard : d2355 pattern = 1) : d1074 pattern ≤ (0 : Int) + d2438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1074, d2438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15035 pattern childGuard
    simpa only [d2355, d1074, d2438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1074, d2438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15036 pattern childGuard
    simpa only [d2355, d1074, d2438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15038 (pattern : Twelve) (guard : d2355 pattern = 1) : d1082 pattern ≤ (0 : Int) + d2439 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1082, d2439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15034 pattern childGuard
    simpa only [d1082, d2439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1082, d2439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15037 pattern childGuard
    simpa only [d1082, d2439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15039 (pattern : Twelve) (guard : d0 pattern = 1) : d1083 pattern ≤ (0 : Int) + d2439 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15040 (pattern : Twelve) (guard : d2356 pattern = 1) : d1090 pattern ≤ (0 : Int) + d2439 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15038 pattern childGuard
    simpa only [d2356, d1090, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15039 pattern childGuard
    simpa only [d2356, d1090, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15041 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (0 : Int) + d6 pattern := by
  change (3 : Int) ≤ (0 : Int) + 6
  decide
theorem c15042 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14969 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15041 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15043 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14969 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15042 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15044 (pattern : Twelve) (guard : d26 pattern = 1) : d34 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c259 pattern childGuard
    simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15043 pattern childGuard
    simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15045 (pattern : Twelve) (guard : d26 pattern = 1) : d36 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c259 pattern childGuard
    simpa only [d26, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d26, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15046 (pattern : Twelve) (guard : d26 pattern = 1) : d827 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15044 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d26 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15045 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15047 (pattern : Twelve) (guard : d2355 pattern = 1) : d1072 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15046 pattern childGuard
    simpa only [d2355, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d2355, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15048 (pattern : Twelve) (guard : d2355 pattern = 1) : d1081 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14975 pattern childGuard
    simpa only [d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15047 pattern childGuard
    simpa only [d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15049 (pattern : Twelve) (guard : d2356 pattern = 1) : d1091 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15048 pattern childGuard
    simpa only [d2356, d1091, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d2356, d1091, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15050 (pattern : Twelve) (guard : d2356 pattern = 1) : d1096 pattern ≤ (0 : Int) + d2481 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1096, d2481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15040 pattern childGuard
    simpa only [d1096, d2481, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1096, d2481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15049 pattern childGuard
    simpa only [d1096, d2481, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15051 (pattern : Twelve) (guard : d2356 pattern = 1) : d1099 pattern ≤ (0 : Int) + d2482 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1099, d2482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15032 pattern childGuard
    simpa only [d1099, d2482, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1099, d2482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15050 pattern childGuard
    simpa only [d1099, d2482, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15052 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2374 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15053 (pattern : Twelve) (guard : d2355 pattern = 1) : d438 pattern ≤ (0 : Int) + d2434 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d438, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14945 pattern childGuard
    simpa only [d2355, d438, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d438, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15052 pattern childGuard
    simpa only [d2355, d438, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15054 (pattern : Twelve) (guard : d2355 pattern = 1) : d1084 pattern ≤ (0 : Int) + d2436 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1084, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15053 pattern childGuard
    simpa only [d1084, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1084, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15028 pattern childGuard
    simpa only [d1084, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15055 (pattern : Twelve) (guard : d2356 pattern = 1) : d1092 pattern ≤ (0 : Int) + d2436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15054 pattern childGuard
    simpa only [d2356, d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15030 pattern childGuard
    simpa only [d2356, d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15056 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2377 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15057 (pattern : Twelve) (guard : d2355 pattern = 1) : d441 pattern ≤ (0 : Int) + d2437 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d441, d2437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14961 pattern childGuard
    simpa only [d2355, d441, d2437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d441, d2437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15056 pattern childGuard
    simpa only [d2355, d441, d2437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15058 (pattern : Twelve) (guard : d2355 pattern = 1) : d1085 pattern ≤ (0 : Int) + d2439 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1085, d2439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15057 pattern childGuard
    simpa only [d1085, d2439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1085, d2439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15037 pattern childGuard
    simpa only [d1085, d2439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15059 (pattern : Twelve) (guard : d2356 pattern = 1) : d1093 pattern ≤ (0 : Int) + d2439 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15058 pattern childGuard
    simpa only [d2356, d1093, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15039 pattern childGuard
    simpa only [d2356, d1093, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15060 (pattern : Twelve) (guard : d2356 pattern = 1) : d1097 pattern ≤ (0 : Int) + d2481 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1097, d2481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15059 pattern childGuard
    simpa only [d1097, d2481, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1097, d2481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15049 pattern childGuard
    simpa only [d1097, d2481, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15061 (pattern : Twelve) (guard : d2356 pattern = 1) : d1100 pattern ≤ (0 : Int) + d2482 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1100, d2482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15055 pattern childGuard
    simpa only [d1100, d2482, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1100, d2482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15060 pattern childGuard
    simpa only [d1100, d2482, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15062 (pattern : Twelve) (guard : d2356 pattern = 1) : d1102 pattern ≤ (0 : Int) + d2482 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15051 pattern childGuard
    simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15061 pattern childGuard
    simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15063 (pattern : Twelve) (guard : d2356 pattern = 1) : d1103 pattern ≤ (0 : Int) + d2482 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15062 pattern childGuard
    simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15061 pattern childGuard
    simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15064 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2384 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15065 (pattern : Twelve) (guard : d2355 pattern = 1) : d441 pattern ≤ (0 : Int) + d2444 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d441, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14961 pattern childGuard
    simpa only [d2355, d441, d2444, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d441, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15064 pattern childGuard
    simpa only [d2355, d441, d2444, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15066 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (0 : Int) + d119 pattern := by
  omega
theorem c15067 (pattern : Twelve) (guard : d26 pattern = 1) : d879 pattern ≤ (0 : Int) + d119 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4744 pattern childGuard
    simpa only [d26, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15066 pattern childGuard
    simpa only [d26, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15068 (pattern : Twelve) (guard : d26 pattern = 1) : d886 pattern ≤ (0 : Int) + d2445 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d886, d2445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15035 pattern childGuard
    simpa only [d886, d2445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d26 pattern = 1 := by simpa only [d886, d2445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15067 pattern childGuard
    simpa only [d886, d2445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15069 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1690 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15070 (pattern : Twelve) (guard : d2355 pattern = 1) : d1076 pattern ≤ (0 : Int) + d2446 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1076, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15068 pattern childGuard
    simpa only [d2355, d1076, d2446, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1076, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15069 pattern childGuard
    simpa only [d2355, d1076, d2446, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15071 (pattern : Twelve) (guard : d2355 pattern = 1) : d1086 pattern ≤ (0 : Int) + d2447 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1086, d2447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15065 pattern childGuard
    simpa only [d1086, d2447, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1086, d2447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15070 pattern childGuard
    simpa only [d1086, d2447, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15072 (pattern : Twelve) (guard : d0 pattern = 1) : d1087 pattern ≤ (0 : Int) + d2447 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15073 (pattern : Twelve) (guard : d2356 pattern = 1) : d1094 pattern ≤ (0 : Int) + d2447 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15071 pattern childGuard
    simpa only [d2356, d1094, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15072 pattern childGuard
    simpa only [d2356, d1094, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15074 (pattern : Twelve) (guard : d2356 pattern = 1) : d1098 pattern ≤ (0 : Int) + d2483 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1098, d2483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15073 pattern childGuard
    simpa only [d1098, d2483, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1098, d2483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15049 pattern childGuard
    simpa only [d1098, d2483, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15075 (pattern : Twelve) (guard : d2356 pattern = 1) : d1101 pattern ≤ (0 : Int) + d2484 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1101, d2484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15055 pattern childGuard
    simpa only [d1101, d2484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1101, d2484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15074 pattern childGuard
    simpa only [d1101, d2484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15076 (pattern : Twelve) (guard : d2356 pattern = 1) : d1104 pattern ≤ (0 : Int) + d2485 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1104, d2485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15063 pattern childGuard
    simpa only [d1104, d2485, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1104, d2485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15075 pattern childGuard
    simpa only [d1104, d2485, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15077 (pattern : Twelve) (guard : d0 pattern = 1) : d908 pattern ≤ (0 : Int) + d2390 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15078 (pattern : Twelve) (guard : d2355 pattern = 1) : d1070 pattern ≤ (0 : Int) + d2452 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1070, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15019 pattern childGuard
    simpa only [d2355, d1070, d2452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1070, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15077 pattern childGuard
    simpa only [d2355, d1070, d2452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15079 (pattern : Twelve) (guard : d2355 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1294 pattern := by
  omega
theorem c15080 (pattern : Twelve) (guard : d2355 pattern = 1) : d1472 pattern ≤ (0 : Int) + d2453 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1472, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15078 pattern childGuard
    simpa only [d1472, d2453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1472, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15079 pattern childGuard
    simpa only [d1472, d2453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15081 (pattern : Twelve) (guard : d0 pattern = 1) : d1473 pattern ≤ (0 : Int) + d2453 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15082 (pattern : Twelve) (guard : d2356 pattern = 1) : d1479 pattern ≤ (0 : Int) + d2453 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15080 pattern childGuard
    simpa only [d2356, d1479, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15081 pattern childGuard
    simpa only [d2356, d1479, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15083 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2390 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15084 (pattern : Twelve) (guard : d2355 pattern = 1) : d1073 pattern ≤ (0 : Int) + d2452 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1073, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15019 pattern childGuard
    simpa only [d2355, d1073, d2452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1073, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15083 pattern childGuard
    simpa only [d2355, d1073, d2452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15085 (pattern : Twelve) (guard : d2355 pattern = 1) : d1474 pattern ≤ (0 : Int) + d2453 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1474, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15084 pattern childGuard
    simpa only [d1474, d2453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1474, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15079 pattern childGuard
    simpa only [d1474, d2453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15086 (pattern : Twelve) (guard : d2356 pattern = 1) : d1480 pattern ≤ (0 : Int) + d2453 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15085 pattern childGuard
    simpa only [d2356, d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15081 pattern childGuard
    simpa only [d2356, d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15087 (pattern : Twelve) (guard : d2356 pattern = 1) : d1484 pattern ≤ (0 : Int) + d2453 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15082 pattern childGuard
    simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15086 pattern childGuard
    simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15088 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2392 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15089 (pattern : Twelve) (guard : d2355 pattern = 1) : d1074 pattern ≤ (0 : Int) + d2454 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1074, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15035 pattern childGuard
    simpa only [d2355, d1074, d2454, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1074, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15088 pattern childGuard
    simpa only [d2355, d1074, d2454, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15090 (pattern : Twelve) (guard : d26 pattern = 1) : d817 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4537 pattern childGuard
    simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c392 pattern childGuard
    simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15091 (pattern : Twelve) (guard : d2355 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15090 pattern childGuard
    simpa only [d2355, d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d2355, d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15092 (pattern : Twelve) (guard : d2355 pattern = 1) : d1475 pattern ≤ (0 : Int) + d2455 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1475, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15089 pattern childGuard
    simpa only [d1475, d2455, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1475, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15091 pattern childGuard
    simpa only [d1475, d2455, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15093 (pattern : Twelve) (guard : d0 pattern = 1) : d1476 pattern ≤ (0 : Int) + d2455 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15094 (pattern : Twelve) (guard : d2356 pattern = 1) : d1481 pattern ≤ (0 : Int) + d2455 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15092 pattern childGuard
    simpa only [d2356, d1481, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15093 pattern childGuard
    simpa only [d2356, d1481, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15095 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14969 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10944 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15096 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15041 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10946 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15097 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15095 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15096 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15098 (pattern : Twelve) (guard : d26 pattern = 1) : d817 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c329 pattern childGuard
    simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15097 pattern childGuard
    simpa only [d26, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15099 (pattern : Twelve) (guard : d26 pattern = 1) : d29 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c329 pattern childGuard
    simpa only [d26, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d26, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15100 (pattern : Twelve) (guard : d26 pattern = 1) : d1286 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15098 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d26 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15099 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15101 (pattern : Twelve) (guard : d2355 pattern = 1) : d1296 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15100 pattern childGuard
    simpa only [d2355, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d2355, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15102 (pattern : Twelve) (guard : d2355 pattern = 1) : d1473 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15047 pattern childGuard
    simpa only [d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15101 pattern childGuard
    simpa only [d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15103 (pattern : Twelve) (guard : d2356 pattern = 1) : d1482 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15102 pattern childGuard
    simpa only [d2356, d1482, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d2356, d1482, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15104 (pattern : Twelve) (guard : d2356 pattern = 1) : d1485 pattern ≤ (0 : Int) + d2486 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1485, d2486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15094 pattern childGuard
    simpa only [d1485, d2486, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1485, d2486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15103 pattern childGuard
    simpa only [d1485, d2486, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15105 (pattern : Twelve) (guard : d2356 pattern = 1) : d1487 pattern ≤ (0 : Int) + d2487 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1487, d2487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15087 pattern childGuard
    simpa only [d1487, d2487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1487, d2487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15104 pattern childGuard
    simpa only [d1487, d2487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15106 (pattern : Twelve) (guard : d2356 pattern = 1) : d1488 pattern ≤ (0 : Int) + d2487 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1488, d2487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15086 pattern childGuard
    simpa only [d1488, d2487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1488, d2487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15104 pattern childGuard
    simpa only [d1488, d2487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15107 (pattern : Twelve) (guard : d2356 pattern = 1) : d1490 pattern ≤ (0 : Int) + d2487 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15105 pattern childGuard
    simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15106 pattern childGuard
    simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15108 (pattern : Twelve) (guard : d2356 pattern = 1) : d1491 pattern ≤ (0 : Int) + d2487 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15107 pattern childGuard
    simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15106 pattern childGuard
    simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15109 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d2398 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15110 (pattern : Twelve) (guard : d2355 pattern = 1) : d1074 pattern ≤ (0 : Int) + d2460 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1074, d2460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15035 pattern childGuard
    simpa only [d2355, d1074, d2460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1074, d2460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15109 pattern childGuard
    simpa only [d2355, d1074, d2460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15111 (pattern : Twelve) (guard : d26 pattern = 1) : d1329 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4825 pattern childGuard
    simpa only [d26, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1536 pattern childGuard
    simpa only [d26, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15112 (pattern : Twelve) (guard : d26 pattern = 1) : d1336 pattern ≤ (0 : Int) + d2461 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d1336, d2461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15090 pattern childGuard
    simpa only [d1336, d2461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d26 pattern = 1 := by simpa only [d1336, d2461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15111 pattern childGuard
    simpa only [d1336, d2461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15113 (pattern : Twelve) (guard : d2355 pattern = 1) : d1342 pattern ≤ (0 : Int) + d2462 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2355, d1342, d2462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15112 pattern childGuard
    simpa only [d2355, d1342, d2462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2355, d1342, d2462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d2355, d1342, d2462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15114 (pattern : Twelve) (guard : d2355 pattern = 1) : d1477 pattern ≤ (0 : Int) + d2463 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1477, d2463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15110 pattern childGuard
    simpa only [d1477, d2463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2355 pattern = 1 := by simpa only [d1477, d2463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15113 pattern childGuard
    simpa only [d1477, d2463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15115 (pattern : Twelve) (guard : d0 pattern = 1) : d1478 pattern ≤ (0 : Int) + d2463 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c15116 (pattern : Twelve) (guard : d2356 pattern = 1) : d1483 pattern ≤ (0 : Int) + d2463 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2355 pattern = 1 := by simpa only [d2356, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15114 pattern childGuard
    simpa only [d2356, d1483, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2356, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15115 pattern childGuard
    simpa only [d2356, d1483, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15117 (pattern : Twelve) (guard : d2356 pattern = 1) : d1486 pattern ≤ (0 : Int) + d2488 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1486, d2488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15116 pattern childGuard
    simpa only [d1486, d2488, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1486, d2488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15103 pattern childGuard
    simpa only [d1486, d2488, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15118 (pattern : Twelve) (guard : d2356 pattern = 1) : d1489 pattern ≤ (0 : Int) + d2489 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1489, d2489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15086 pattern childGuard
    simpa only [d1489, d2489, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1489, d2489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15117 pattern childGuard
    simpa only [d1489, d2489, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15119 (pattern : Twelve) (guard : d2356 pattern = 1) : d1492 pattern ≤ (0 : Int) + d2490 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1492, d2490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15108 pattern childGuard
    simpa only [d1492, d2490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2356 pattern = 1 := by simpa only [d1492, d2490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15118 pattern childGuard
    simpa only [d1492, d2490, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
