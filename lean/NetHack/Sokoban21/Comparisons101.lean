/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons100
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c14140 (pattern : Twelve) (guard : d0 pattern = 1) : d1455 pattern ≤ (0 : Int) + d1305 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14141 (pattern : Twelve) (guard : d2279 pattern = 1) : d1459 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14140 pattern childGuard
    simpa only [d2279, d1459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5659 pattern childGuard
    simpa only [d2279, d1459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14142 (pattern : Twelve) (guard : d0 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1305 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14143 (pattern : Twelve) (guard : d2279 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14142 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5659 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14144 (pattern : Twelve) (guard : d2279 pattern = 1) : d1463 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14141 pattern childGuard
    simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2279 pattern = 1 := by simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14143 pattern childGuard
    simpa only [d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14145 (pattern : Twelve) (guard : d0 pattern = 1) : d1464 pattern ≤ (0 : Int) + d1305 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14146 (pattern : Twelve) (guard : d2280 pattern = 1) : d1466 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14144 pattern childGuard
    simpa only [d2280, d1466, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14145 pattern childGuard
    simpa only [d2280, d1466, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14147 (pattern : Twelve) (guard : d0 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1309 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14148 (pattern : Twelve) (guard : d2279 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1309 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14147 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5832 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14149 (pattern : Twelve) (guard : d0 pattern = 1) : d1464 pattern ≤ (0 : Int) + d1309 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14150 (pattern : Twelve) (guard : d2280 pattern = 1) : d1467 pattern ≤ (0 : Int) + d1309 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14148 pattern childGuard
    simpa only [d2280, d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14149 pattern childGuard
    simpa only [d2280, d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14151 (pattern : Twelve) (guard : d2280 pattern = 1) : d1469 pattern ≤ (0 : Int) + d2300 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1469, d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14146 pattern childGuard
    simpa only [d1469, d2300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1469, d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14150 pattern childGuard
    simpa only [d1469, d2300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14152 (pattern : Twelve) (guard : d2280 pattern = 1) : d1467 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14143 pattern childGuard
    simpa only [d2280, d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14145 pattern childGuard
    simpa only [d2280, d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14153 (pattern : Twelve) (guard : d2280 pattern = 1) : d1467 pattern ≤ (0 : Int) + d2300 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14152 pattern childGuard
    simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14150 pattern childGuard
    simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14154 (pattern : Twelve) (guard : d2280 pattern = 1) : d1470 pattern ≤ (0 : Int) + d2300 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14151 pattern childGuard
    simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14153 pattern childGuard
    simpa only [d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14155 (pattern : Twelve) (guard : d0 pattern = 1) : d1465 pattern ≤ (0 : Int) + d1305 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14156 (pattern : Twelve) (guard : d2280 pattern = 1) : d1468 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14143 pattern childGuard
    simpa only [d2280, d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14155 pattern childGuard
    simpa only [d2280, d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14157 (pattern : Twelve) (guard : d0 pattern = 1) : d1465 pattern ≤ (0 : Int) + d1309 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14158 (pattern : Twelve) (guard : d2280 pattern = 1) : d1468 pattern ≤ (0 : Int) + d1309 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14148 pattern childGuard
    simpa only [d2280, d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14157 pattern childGuard
    simpa only [d2280, d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14159 (pattern : Twelve) (guard : d2280 pattern = 1) : d1468 pattern ≤ (0 : Int) + d2300 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14156 pattern childGuard
    simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14158 pattern childGuard
    simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14160 (pattern : Twelve) (guard : d2280 pattern = 1) : d1471 pattern ≤ (0 : Int) + d2300 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14154 pattern childGuard
    simpa only [d1471, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14159 pattern childGuard
    simpa only [d1471, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14161 (pattern : Twelve) (guard : d0 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1656 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14162 (pattern : Twelve) (guard : d2279 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14161 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5704 pattern childGuard
    simpa only [d2279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14163 (pattern : Twelve) (guard : d0 pattern = 1) : d1725 pattern ≤ (0 : Int) + d1656 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14164 (pattern : Twelve) (guard : d2280 pattern = 1) : d1727 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14162 pattern childGuard
    simpa only [d2280, d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14163 pattern childGuard
    simpa only [d2280, d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14165 (pattern : Twelve) (guard : d0 pattern = 1) : d1726 pattern ≤ (0 : Int) + d1656 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14166 (pattern : Twelve) (guard : d2280 pattern = 1) : d1728 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2279 pattern = 1 := by simpa only [d2280, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14162 pattern childGuard
    simpa only [d2280, d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2280, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14165 pattern childGuard
    simpa only [d2280, d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14167 (pattern : Twelve) (guard : d2280 pattern = 1) : d1729 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14164 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2280 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14166 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14168 (pattern : Twelve) (guard : d2301 pattern = 1) : d0 pattern ≤ (2 : Int) + d0 pattern := by
  omega
theorem c14169 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (2 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14170 (pattern : Twelve) (guard : d26 pattern = 1) : d26 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14169 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13322 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14171 (pattern : Twelve) (guard : d0 pattern = 1) : d27 pattern ≤ (2 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14172 (pattern : Twelve) (guard : d2301 pattern = 1) : d50 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14170 pattern childGuard
    simpa only [d2301, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14171 pattern childGuard
    simpa only [d2301, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14173 (pattern : Twelve) (guard : d2301 pattern = 1) : d72 pattern ≤ (2 : Int) + d2302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d72, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14168 pattern childGuard
    simpa only [d72, d2302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d72, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14172 pattern childGuard
    simpa only [d72, d2302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14174 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (2 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14175 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13319 pattern childGuard
    simpa only [d8, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d8, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14176 (pattern : Twelve) (guard : d1 pattern = 1) : d18 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14175 pattern childGuard
    simpa only [d18, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13332 pattern childGuard
    simpa only [d18, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14177 (pattern : Twelve) (guard : d26 pattern = 1) : d28 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14174 pattern childGuard
    simpa only [d26, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14176 pattern childGuard
    simpa only [d26, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14178 (pattern : Twelve) (guard : d0 pattern = 1) : d29 pattern ≤ (2 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14179 (pattern : Twelve) (guard : d2301 pattern = 1) : d51 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14177 pattern childGuard
    simpa only [d2301, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14178 pattern childGuard
    simpa only [d2301, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14180 (pattern : Twelve) (guard : d2301 pattern = 1) : d73 pattern ≤ (2 : Int) + d2303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d73, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14168 pattern childGuard
    simpa only [d73, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d73, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14179 pattern childGuard
    simpa only [d73, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14181 (pattern : Twelve) (guard : d2301 pattern = 1) : d91 pattern ≤ (2 : Int) + d2304 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d91, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14173 pattern childGuard
    simpa only [d91, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d91, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14180 pattern childGuard
    simpa only [d91, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14182 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14183 (pattern : Twelve) (guard : d26 pattern = 1) : d30 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14182 pattern childGuard
    simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13281 pattern childGuard
    simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14184 (pattern : Twelve) (guard : d0 pattern = 1) : d31 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14185 (pattern : Twelve) (guard : d2301 pattern = 1) : d52 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14183 pattern childGuard
    simpa only [d2301, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14184 pattern childGuard
    simpa only [d2301, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14186 (pattern : Twelve) (guard : d26 pattern = 1) : d30 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14169 pattern childGuard
    simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13393 pattern childGuard
    simpa only [d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14187 (pattern : Twelve) (guard : d0 pattern = 1) : d32 pattern ≤ (2 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14188 (pattern : Twelve) (guard : d2301 pattern = 1) : d53 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14186 pattern childGuard
    simpa only [d2301, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14187 pattern childGuard
    simpa only [d2301, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14189 (pattern : Twelve) (guard : d2301 pattern = 1) : d74 pattern ≤ (2 : Int) + d2302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d74, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14185 pattern childGuard
    simpa only [d74, d2302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d74, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14188 pattern childGuard
    simpa only [d74, d2302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14190 (pattern : Twelve) (guard : d0 pattern = 1) : d33 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14191 (pattern : Twelve) (guard : d2301 pattern = 1) : d54 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14183 pattern childGuard
    simpa only [d2301, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14190 pattern childGuard
    simpa only [d2301, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14192 (pattern : Twelve) (guard : d26 pattern = 1) : d34 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14174 pattern childGuard
    simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13333 pattern childGuard
    simpa only [d26, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14193 (pattern : Twelve) (guard : d2301 pattern = 1) : d55 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14192 pattern childGuard
    simpa only [d2301, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14178 pattern childGuard
    simpa only [d2301, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14194 (pattern : Twelve) (guard : d2301 pattern = 1) : d75 pattern ≤ (2 : Int) + d2303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d75, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14191 pattern childGuard
    simpa only [d75, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d75, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14193 pattern childGuard
    simpa only [d75, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14195 (pattern : Twelve) (guard : d2301 pattern = 1) : d92 pattern ≤ (2 : Int) + d2304 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d92, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14189 pattern childGuard
    simpa only [d92, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d92, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14194 pattern childGuard
    simpa only [d92, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14196 (pattern : Twelve) (guard : d2301 pattern = 1) : d102 pattern ≤ (2 : Int) + d2304 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14181 pattern childGuard
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14195 pattern childGuard
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14197 (pattern : Twelve) (guard : d2301 pattern = 1) : d76 pattern ≤ (2 : Int) + d2303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d76, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14168 pattern childGuard
    simpa only [d76, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d76, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14193 pattern childGuard
    simpa only [d76, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14198 (pattern : Twelve) (guard : d2301 pattern = 1) : d93 pattern ≤ (2 : Int) + d2304 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d93, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14173 pattern childGuard
    simpa only [d93, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d93, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14197 pattern childGuard
    simpa only [d93, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14199 (pattern : Twelve) (guard : d0 pattern = 1) : d35 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14200 (pattern : Twelve) (guard : d2301 pattern = 1) : d56 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14183 pattern childGuard
    simpa only [d2301, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14199 pattern childGuard
    simpa only [d2301, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14201 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (2 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14202 (pattern : Twelve) (guard : d2301 pattern = 1) : d57 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14186 pattern childGuard
    simpa only [d2301, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14201 pattern childGuard
    simpa only [d2301, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14203 (pattern : Twelve) (guard : d2301 pattern = 1) : d77 pattern ≤ (2 : Int) + d2302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d77, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14200 pattern childGuard
    simpa only [d77, d2302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d77, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14202 pattern childGuard
    simpa only [d77, d2302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14204 (pattern : Twelve) (guard : d2301 pattern = 1) : d78 pattern ≤ (2 : Int) + d2303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d78, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14200 pattern childGuard
    simpa only [d78, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d78, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14193 pattern childGuard
    simpa only [d78, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14205 (pattern : Twelve) (guard : d2301 pattern = 1) : d94 pattern ≤ (2 : Int) + d2304 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d94, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14203 pattern childGuard
    simpa only [d94, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d94, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14204 pattern childGuard
    simpa only [d94, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14206 (pattern : Twelve) (guard : d2301 pattern = 1) : d103 pattern ≤ (2 : Int) + d2304 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14198 pattern childGuard
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14205 pattern childGuard
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14207 (pattern : Twelve) (guard : d2301 pattern = 1) : d110 pattern ≤ (2 : Int) + d2304 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14196 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14206 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14208 (pattern : Twelve) (guard : d0 pattern = 1) : d30 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14209 (pattern : Twelve) (guard : d2301 pattern = 1) : d30 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14183 pattern childGuard
    simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14208 pattern childGuard
    simpa only [d2301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14210 (pattern : Twelve) (guard : d0 pattern = 1) : d37 pattern ≤ (2 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14211 (pattern : Twelve) (guard : d2301 pattern = 1) : d58 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14186 pattern childGuard
    simpa only [d2301, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14210 pattern childGuard
    simpa only [d2301, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14212 (pattern : Twelve) (guard : d2301 pattern = 1) : d79 pattern ≤ (2 : Int) + d2302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d79, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14209 pattern childGuard
    simpa only [d79, d2302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d79, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14211 pattern childGuard
    simpa only [d79, d2302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14213 (pattern : Twelve) (guard : d2301 pattern = 1) : d80 pattern ≤ (2 : Int) + d2303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d80, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14209 pattern childGuard
    simpa only [d80, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d80, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14193 pattern childGuard
    simpa only [d80, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14214 (pattern : Twelve) (guard : d2301 pattern = 1) : d95 pattern ≤ (2 : Int) + d2304 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d95, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14212 pattern childGuard
    simpa only [d95, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d95, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14213 pattern childGuard
    simpa only [d95, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14215 (pattern : Twelve) (guard : d26 pattern = 1) : d38 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13953 pattern childGuard
    simpa only [d26, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d26, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14216 (pattern : Twelve) (guard : d0 pattern = 1) : d39 pattern ≤ (2 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14217 (pattern : Twelve) (guard : d2301 pattern = 1) : d59 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14215 pattern childGuard
    simpa only [d2301, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14216 pattern childGuard
    simpa only [d2301, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14218 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (2 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14219 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d3 pattern := by
  change (4 : Int) ≤ (2 : Int) + 3
  decide
theorem c14220 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14219 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14221 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14220 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14222 (pattern : Twelve) (guard : d26 pattern = 1) : d38 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14218 pattern childGuard
    simpa only [d26, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14221 pattern childGuard
    simpa only [d26, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14223 (pattern : Twelve) (guard : d0 pattern = 1) : d40 pattern ≤ (2 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14224 (pattern : Twelve) (guard : d2301 pattern = 1) : d60 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14222 pattern childGuard
    simpa only [d2301, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14223 pattern childGuard
    simpa only [d2301, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14225 (pattern : Twelve) (guard : d2301 pattern = 1) : d81 pattern ≤ (2 : Int) + d1943 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d81, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14217 pattern childGuard
    simpa only [d81, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d81, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14224 pattern childGuard
    simpa only [d81, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14226 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (2 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14227 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d4 pattern := by
  omega
theorem c14228 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14227 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14229 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (2 : Int) + d5 pattern := by
  omega
theorem c14230 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (2 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14219 pattern childGuard
    simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14229 pattern childGuard
    simpa only [d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14231 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14228 pattern childGuard
    simpa only [d24, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14230 pattern childGuard
    simpa only [d24, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14232 (pattern : Twelve) (guard : d26 pattern = 1) : d41 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14226 pattern childGuard
    simpa only [d26, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14231 pattern childGuard
    simpa only [d26, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14233 (pattern : Twelve) (guard : d0 pattern = 1) : d42 pattern ≤ (2 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14234 (pattern : Twelve) (guard : d2301 pattern = 1) : d61 pattern ≤ (2 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14232 pattern childGuard
    simpa only [d2301, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14233 pattern childGuard
    simpa only [d2301, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14235 (pattern : Twelve) (guard : d2301 pattern = 1) : d82 pattern ≤ (2 : Int) + d1971 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d82, d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14217 pattern childGuard
    simpa only [d82, d1971, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d82, d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14234 pattern childGuard
    simpa only [d82, d1971, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14236 (pattern : Twelve) (guard : d2301 pattern = 1) : d96 pattern ≤ (2 : Int) + d2305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d96, d2305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14225 pattern childGuard
    simpa only [d96, d2305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d96, d2305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14235 pattern childGuard
    simpa only [d96, d2305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14237 (pattern : Twelve) (guard : d2301 pattern = 1) : d104 pattern ≤ (2 : Int) + d2306 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d104, d2306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14214 pattern childGuard
    simpa only [d104, d2306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d104, d2306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14236 pattern childGuard
    simpa only [d104, d2306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14238 (pattern : Twelve) (guard : d2301 pattern = 1) : d6 pattern ≤ (2 : Int) + d6 pattern := by
  omega
theorem c14239 (pattern : Twelve) (guard : d2301 pattern = 1) : d105 pattern ≤ (2 : Int) + d2307 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d105, d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14205 pattern childGuard
    simpa only [d105, d2307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d105, d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d105, d2307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14240 (pattern : Twelve) (guard : d2301 pattern = 1) : d111 pattern ≤ (2 : Int) + d2308 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d111, d2308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14237 pattern childGuard
    simpa only [d111, d2308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d111, d2308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14239 pattern childGuard
    simpa only [d111, d2308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14241 (pattern : Twelve) (guard : d2301 pattern = 1) : d114 pattern ≤ (2 : Int) + d2309 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d114, d2309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14207 pattern childGuard
    simpa only [d114, d2309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d114, d2309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14240 pattern childGuard
    simpa only [d114, d2309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14242 (pattern : Twelve) (guard : d26 pattern = 1) : d120 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14174 pattern childGuard
    simpa only [d26, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13309 pattern childGuard
    simpa only [d26, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14243 (pattern : Twelve) (guard : d2301 pattern = 1) : d129 pattern ≤ (2 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14242 pattern childGuard
    simpa only [d2301, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14178 pattern childGuard
    simpa only [d2301, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14244 (pattern : Twelve) (guard : d2301 pattern = 1) : d136 pattern ≤ (2 : Int) + d2303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d136, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14168 pattern childGuard
    simpa only [d136, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d136, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14243 pattern childGuard
    simpa only [d136, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14245 (pattern : Twelve) (guard : d2301 pattern = 1) : d144 pattern ≤ (2 : Int) + d2304 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d144, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14173 pattern childGuard
    simpa only [d144, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d144, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14244 pattern childGuard
    simpa only [d144, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14246 (pattern : Twelve) (guard : d26 pattern = 1) : d121 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14169 pattern childGuard
    simpa only [d26, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13299 pattern childGuard
    simpa only [d26, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14247 (pattern : Twelve) (guard : d2301 pattern = 1) : d130 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14246 pattern childGuard
    simpa only [d2301, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14201 pattern childGuard
    simpa only [d2301, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14248 (pattern : Twelve) (guard : d2301 pattern = 1) : d137 pattern ≤ (2 : Int) + d2302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d137, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14185 pattern childGuard
    simpa only [d137, d2302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d137, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14247 pattern childGuard
    simpa only [d137, d2302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14249 (pattern : Twelve) (guard : d2301 pattern = 1) : d138 pattern ≤ (2 : Int) + d2303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d138, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14200 pattern childGuard
    simpa only [d138, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d138, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14243 pattern childGuard
    simpa only [d138, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14250 (pattern : Twelve) (guard : d2301 pattern = 1) : d145 pattern ≤ (2 : Int) + d2304 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d145, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14248 pattern childGuard
    simpa only [d145, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d145, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14249 pattern childGuard
    simpa only [d145, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14251 (pattern : Twelve) (guard : d2301 pattern = 1) : d149 pattern ≤ (2 : Int) + d2304 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14245 pattern childGuard
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14250 pattern childGuard
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14252 (pattern : Twelve) (guard : d2301 pattern = 1) : d139 pattern ≤ (2 : Int) + d2302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d139, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14200 pattern childGuard
    simpa only [d139, d2302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d139, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14247 pattern childGuard
    simpa only [d139, d2302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14253 (pattern : Twelve) (guard : d2301 pattern = 1) : d146 pattern ≤ (2 : Int) + d2304 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d146, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14252 pattern childGuard
    simpa only [d146, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d146, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14249 pattern childGuard
    simpa only [d146, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14254 (pattern : Twelve) (guard : d2301 pattern = 1) : d150 pattern ≤ (2 : Int) + d2304 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14245 pattern childGuard
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14253 pattern childGuard
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14255 (pattern : Twelve) (guard : d2301 pattern = 1) : d153 pattern ≤ (2 : Int) + d2304 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14251 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14254 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14256 (pattern : Twelve) (guard : d0 pattern = 1) : d122 pattern ≤ (2 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14257 (pattern : Twelve) (guard : d2301 pattern = 1) : d131 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14246 pattern childGuard
    simpa only [d2301, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14256 pattern childGuard
    simpa only [d2301, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14258 (pattern : Twelve) (guard : d2301 pattern = 1) : d140 pattern ≤ (2 : Int) + d2302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d140, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14209 pattern childGuard
    simpa only [d140, d2302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d140, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14257 pattern childGuard
    simpa only [d140, d2302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14259 (pattern : Twelve) (guard : d0 pattern = 1) : d123 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14260 (pattern : Twelve) (guard : d2301 pattern = 1) : d132 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14183 pattern childGuard
    simpa only [d2301, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14259 pattern childGuard
    simpa only [d2301, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14261 (pattern : Twelve) (guard : d2301 pattern = 1) : d141 pattern ≤ (2 : Int) + d2303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d141, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14260 pattern childGuard
    simpa only [d141, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d141, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14243 pattern childGuard
    simpa only [d141, d2303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14262 (pattern : Twelve) (guard : d2301 pattern = 1) : d147 pattern ≤ (2 : Int) + d2304 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d147, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14258 pattern childGuard
    simpa only [d147, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d147, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14261 pattern childGuard
    simpa only [d147, d2304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14263 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (2 : Int) + d119 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14264 (pattern : Twelve) (guard : d1 pattern = 1) : d118 pattern ≤ (2 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13303 pattern childGuard
    simpa only [d118, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13423 pattern childGuard
    simpa only [d118, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14265 (pattern : Twelve) (guard : d26 pattern = 1) : d124 pattern ≤ (2 : Int) + d119 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14263 pattern childGuard
    simpa only [d26, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14264 pattern childGuard
    simpa only [d26, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14266 (pattern : Twelve) (guard : d0 pattern = 1) : d125 pattern ≤ (2 : Int) + d119 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14267 (pattern : Twelve) (guard : d2301 pattern = 1) : d133 pattern ≤ (2 : Int) + d119 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14265 pattern childGuard
    simpa only [d2301, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14266 pattern childGuard
    simpa only [d2301, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14268 (pattern : Twelve) (guard : d2301 pattern = 1) : d142 pattern ≤ (2 : Int) + d2310 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d142, d2310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14217 pattern childGuard
    simpa only [d142, d2310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d142, d2310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14267 pattern childGuard
    simpa only [d142, d2310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14269 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (2 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14270 (pattern : Twelve) (guard : d26 pattern = 1) : d126 pattern ≤ (2 : Int) + d3 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14269 pattern childGuard
    simpa only [d26, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13303 pattern childGuard
    simpa only [d26, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14271 (pattern : Twelve) (guard : d0 pattern = 1) : d47 pattern ≤ (2 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14272 (pattern : Twelve) (guard : d2301 pattern = 1) : d134 pattern ≤ (2 : Int) + d3 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14270 pattern childGuard
    simpa only [d2301, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14271 pattern childGuard
    simpa only [d2301, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14273 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (2 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14274 (pattern : Twelve) (guard : d26 pattern = 1) : d127 pattern ≤ (2 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14273 pattern childGuard
    simpa only [d26, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13463 pattern childGuard
    simpa only [d26, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14275 (pattern : Twelve) (guard : d0 pattern = 1) : d128 pattern ≤ (2 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14276 (pattern : Twelve) (guard : d2301 pattern = 1) : d135 pattern ≤ (2 : Int) + d20 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14274 pattern childGuard
    simpa only [d2301, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14275 pattern childGuard
    simpa only [d2301, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14277 (pattern : Twelve) (guard : d2301 pattern = 1) : d143 pattern ≤ (2 : Int) + d2311 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d143, d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14272 pattern childGuard
    simpa only [d143, d2311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d143, d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14276 pattern childGuard
    simpa only [d143, d2311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14278 (pattern : Twelve) (guard : d2301 pattern = 1) : d148 pattern ≤ (2 : Int) + d2312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d148, d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14268 pattern childGuard
    simpa only [d148, d2312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d148, d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14277 pattern childGuard
    simpa only [d148, d2312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14279 (pattern : Twelve) (guard : d2301 pattern = 1) : d151 pattern ≤ (2 : Int) + d2313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d151, d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14262 pattern childGuard
    simpa only [d151, d2313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d151, d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14278 pattern childGuard
    simpa only [d151, d2313, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
