/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons14
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c2400 (pattern : Ten) (guard : d350 pattern = 1) : d47 pattern ≤ (2 : Int) + d46 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2399 pattern childGuard
    simpa only [d47, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d47, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2401 (pattern : Ten) (guard : d350 pattern = 1) : d53 pattern ≤ (2 : Int) + d52 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2400 pattern childGuard
    simpa only [d53, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d53, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2402 (pattern : Ten) (guard : d350 pattern = 1) : d57 pattern ≤ (2 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2401 pattern childGuard
    simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d57, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2403 (pattern : Ten) (guard : d350 pattern = 1) : d61 pattern ≤ (2 : Int) + d60 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2402 pattern childGuard
    simpa only [d61, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d61, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2404 (pattern : Ten) (guard : d432 pattern = 1) : d63 pattern ≤ (2 : Int) + d60 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d432, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2393 pattern childGuard
    simpa only [d432, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d432, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2403 pattern childGuard
    simpa only [d432, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2405 (pattern : Ten) (guard : d432 pattern = 1) : d65 pattern ≤ (2 : Int) + d84 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d432 pattern = 1 := by simpa only [d65, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2392 pattern childGuard
    simpa only [d65, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d432 pattern = 1 := by simpa only [d65, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2404 pattern childGuard
    simpa only [d65, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2406 (pattern : Ten) (guard : d432 pattern = 1) : d66 pattern ≤ (2 : Int) + d440 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d432 pattern = 1 := by simpa only [d66, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2391 pattern childGuard
    simpa only [d66, d440, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d432 pattern = 1 := by simpa only [d66, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2405 pattern childGuard
    simpa only [d66, d440, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2407 (pattern : Ten) (guard : d355 pattern = 1) : d207 pattern ≤ (2 : Int) + d207 pattern := by
  omega
theorem c2408 (pattern : Ten) (guard : d0 pattern = 1) : d211 pattern ≤ (2 : Int) + d211 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2409 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d0 pattern := by
  change (2 : Int) ≤ (2 : Int) + 0
  decide
theorem c2410 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d1 pattern := by
  change (3 : Int) ≤ (2 : Int) + 1
  decide
theorem c2411 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (2 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2409 pattern childGuard
    simpa only [d172, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2410 pattern childGuard
    simpa only [d172, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2412 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d2 pattern := by
  change (4 : Int) ≤ (2 : Int) + 2
  decide
theorem c2413 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (2 : Int) + d3 pattern := by
  change (5 : Int) ≤ (2 : Int) + 3
  decide
theorem c2414 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (2 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2412 pattern childGuard
    simpa only [d193, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2413 pattern childGuard
    simpa only [d193, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2415 (pattern : Ten) (guard : d1 pattern = 1) : d199 pattern ≤ (2 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d199, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2411 pattern childGuard
    simpa only [d199, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d199, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2414 pattern childGuard
    simpa only [d199, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2416 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d4 pattern := by
  change (6 : Int) ≤ (2 : Int) + 4
  decide
theorem c2417 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (2 : Int) + d5 pattern := by
  change (7 : Int) ≤ (2 : Int) + 5
  decide
theorem c2418 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (2 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2416 pattern childGuard
    simpa only [d194, d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2417 pattern childGuard
    simpa only [d194, d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2419 (pattern : Ten) (guard : d1 pattern = 1) : d198 pattern ≤ (2 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2418 pattern childGuard
    simpa only [d198, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d198, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2420 (pattern : Ten) (guard : d1 pattern = 1) : d204 pattern ≤ (2 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d204, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2415 pattern childGuard
    simpa only [d204, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d204, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2419 pattern childGuard
    simpa only [d204, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2421 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (2 : Int) + d6 pattern := by
  change (8 : Int) ≤ (2 : Int) + 6
  decide
theorem c2422 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (2 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2421 pattern childGuard
    simpa only [d195, d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2394 pattern childGuard
    simpa only [d195, d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2423 (pattern : Ten) (guard : d1 pattern = 1) : d200 pattern ≤ (2 : Int) + d198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2422 pattern childGuard
    simpa only [d200, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d200, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2424 (pattern : Ten) (guard : d1 pattern = 1) : d205 pattern ≤ (2 : Int) + d203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2423 pattern childGuard
    simpa only [d205, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d205, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2425 (pattern : Ten) (guard : d1 pattern = 1) : d208 pattern ≤ (2 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d208, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2420 pattern childGuard
    simpa only [d208, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d208, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2424 pattern childGuard
    simpa only [d208, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2426 (pattern : Ten) (guard : d1 pattern = 1) : d212 pattern ≤ (2 : Int) + d211 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d212, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2425 pattern childGuard
    simpa only [d212, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d212, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d212, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2427 (pattern : Ten) (guard : d355 pattern = 1) : d215 pattern ≤ (2 : Int) + d211 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d355, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2408 pattern childGuard
    simpa only [d355, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d355, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2426 pattern childGuard
    simpa only [d355, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2428 (pattern : Ten) (guard : d355 pattern = 1) : d218 pattern ≤ (2 : Int) + d434 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d355 pattern = 1 := by simpa only [d218, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2407 pattern childGuard
    simpa only [d218, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d355 pattern = 1 := by simpa only [d218, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2427 pattern childGuard
    simpa only [d218, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2429 (pattern : Ten) (guard : d0 pattern = 1) : d209 pattern ≤ (2 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2430 (pattern : Ten) (guard : d1 pattern = 1) : d209 pattern ≤ (2 : Int) + d209 pattern := by
  omega
theorem c2431 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (2 : Int) + d195 pattern := by
  omega
theorem c2432 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (2 : Int) + d8 pattern := by
  change (9 : Int) ≤ (2 : Int) + 8
  decide
theorem c2433 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d9 pattern := by
  change (10 : Int) ≤ (2 : Int) + 9
  decide
theorem c2434 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (2 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2432 pattern childGuard
    simpa only [d11, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2433 pattern childGuard
    simpa only [d11, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2435 (pattern : Ten) (guard : d1 pattern = 1) : d196 pattern ≤ (2 : Int) + d195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2431 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2434 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2436 (pattern : Ten) (guard : d1 pattern = 1) : d201 pattern ≤ (2 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2435 pattern childGuard
    simpa only [d201, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d201, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2437 (pattern : Ten) (guard : d1 pattern = 1) : d206 pattern ≤ (2 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2436 pattern childGuard
    simpa only [d206, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d206, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2438 (pattern : Ten) (guard : d1 pattern = 1) : d210 pattern ≤ (2 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2437 pattern childGuard
    simpa only [d210, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d210, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2439 (pattern : Ten) (guard : d1 pattern = 1) : d213 pattern ≤ (2 : Int) + d209 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2430 pattern childGuard
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2438 pattern childGuard
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2440 (pattern : Ten) (guard : d355 pattern = 1) : d216 pattern ≤ (2 : Int) + d209 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d355, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2429 pattern childGuard
    simpa only [d355, d216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d355, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2439 pattern childGuard
    simpa only [d355, d216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2441 (pattern : Ten) (guard : d0 pattern = 1) : d214 pattern ≤ (2 : Int) + d214 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2442 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2395 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2433 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2443 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2442 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2444 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2443 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2445 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2444 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2446 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2445 pattern childGuard
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2447 (pattern : Ten) (guard : d355 pattern = 1) : d217 pattern ≤ (2 : Int) + d214 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d355, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2441 pattern childGuard
    simpa only [d355, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d355, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2446 pattern childGuard
    simpa only [d355, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2448 (pattern : Ten) (guard : d355 pattern = 1) : d219 pattern ≤ (2 : Int) + d237 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d355 pattern = 1 := by simpa only [d219, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2440 pattern childGuard
    simpa only [d219, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d355 pattern = 1 := by simpa only [d219, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2447 pattern childGuard
    simpa only [d219, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2449 (pattern : Ten) (guard : d355 pattern = 1) : d220 pattern ≤ (2 : Int) + d435 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d355 pattern = 1 := by simpa only [d220, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2428 pattern childGuard
    simpa only [d220, d435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d355 pattern = 1 := by simpa only [d220, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2448 pattern childGuard
    simpa only [d220, d435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2450 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (1 : Int) + d171 pattern := by
  omega
theorem c2451 (pattern : Ten) (guard : d350 pattern = 1) : d292 pattern ≤ (1 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2450 pattern childGuard
    simpa only [d350, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1850 pattern childGuard
    simpa only [d350, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2452 (pattern : Ten) (guard : d350 pattern = 1) : d172 pattern ≤ (1 : Int) + d172 pattern := by
  omega
theorem c2453 (pattern : Ten) (guard : d350 pattern = 1) : d293 pattern ≤ (1 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d293, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2451 pattern childGuard
    simpa only [d293, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d293, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2452 pattern childGuard
    simpa only [d293, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2454 (pattern : Ten) (guard : d350 pattern = 1) : d197 pattern ≤ (1 : Int) + d197 pattern := by
  omega
theorem c2455 (pattern : Ten) (guard : d350 pattern = 1) : d294 pattern ≤ (1 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d294, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2453 pattern childGuard
    simpa only [d294, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d294, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2454 pattern childGuard
    simpa only [d294, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2456 (pattern : Ten) (guard : d350 pattern = 1) : d203 pattern ≤ (1 : Int) + d203 pattern := by
  omega
theorem c2457 (pattern : Ten) (guard : d350 pattern = 1) : d295 pattern ≤ (1 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d295, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2455 pattern childGuard
    simpa only [d295, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d295, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2456 pattern childGuard
    simpa only [d295, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2458 (pattern : Ten) (guard : d350 pattern = 1) : d207 pattern ≤ (1 : Int) + d207 pattern := by
  omega
theorem c2459 (pattern : Ten) (guard : d350 pattern = 1) : d296 pattern ≤ (1 : Int) + d207 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2457 pattern childGuard
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2458 pattern childGuard
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2460 (pattern : Ten) (guard : d350 pattern = 1) : d297 pattern ≤ (1 : Int) + d207 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2459 pattern childGuard
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2458 pattern childGuard
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2461 (pattern : Ten) (guard : d350 pattern = 1) : d215 pattern ≤ (1 : Int) + d215 pattern := by
  omega
theorem c2462 (pattern : Ten) (guard : d350 pattern = 1) : d298 pattern ≤ (1 : Int) + d218 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d298, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2460 pattern childGuard
    simpa only [d298, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d298, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2461 pattern childGuard
    simpa only [d298, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2463 (pattern : Ten) (guard : d350 pattern = 1) : d209 pattern ≤ (1 : Int) + d209 pattern := by
  omega
theorem c2464 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (1 : Int) + d195 pattern := by
  omega
theorem c2465 (pattern : Ten) (guard : d0 pattern = 1) : d195 pattern ≤ (1 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2466 (pattern : Ten) (guard : d350 pattern = 1) : d195 pattern ≤ (1 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2464 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2465 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2467 (pattern : Ten) (guard : d350 pattern = 1) : d200 pattern ≤ (1 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d200, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2466 pattern childGuard
    simpa only [d200, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d200, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d200, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2468 (pattern : Ten) (guard : d350 pattern = 1) : d205 pattern ≤ (1 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d205, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2467 pattern childGuard
    simpa only [d205, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d205, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d205, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2469 (pattern : Ten) (guard : d350 pattern = 1) : d209 pattern ≤ (1 : Int) + d210 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d209, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2468 pattern childGuard
    simpa only [d209, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d209, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d209, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2470 (pattern : Ten) (guard : d350 pattern = 1) : d209 pattern ≤ (1 : Int) + d213 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2463 pattern childGuard
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2469 pattern childGuard
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2471 (pattern : Ten) (guard : d350 pattern = 1) : d209 pattern ≤ (1 : Int) + d216 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2463 pattern childGuard
    simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2470 pattern childGuard
    simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2472 (pattern : Ten) (guard : d350 pattern = 1) : d217 pattern ≤ (1 : Int) + d217 pattern := by
  omega
theorem c2473 (pattern : Ten) (guard : d350 pattern = 1) : d299 pattern ≤ (1 : Int) + d219 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d299, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2471 pattern childGuard
    simpa only [d299, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d299, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2472 pattern childGuard
    simpa only [d299, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2474 (pattern : Ten) (guard : d350 pattern = 1) : d300 pattern ≤ (1 : Int) + d220 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d300, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2462 pattern childGuard
    simpa only [d300, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d300, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2473 pattern childGuard
    simpa only [d300, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2475 (pattern : Ten) (guard : d350 pattern = 1) : d218 pattern ≤ (1 : Int) + d218 pattern := by
  omega
theorem c2476 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (1 : Int) + d9 pattern := by
  change (8 : Int) ≤ (1 : Int) + 9
  decide
theorem c2477 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (1 : Int) + d11 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2476 pattern childGuard
    simpa only [d195, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1857 pattern childGuard
    simpa only [d195, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2478 (pattern : Ten) (guard : d0 pattern = 1) : d11 pattern ≤ (1 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2479 (pattern : Ten) (guard : d350 pattern = 1) : d196 pattern ≤ (1 : Int) + d11 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2477 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2478 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2480 (pattern : Ten) (guard : d350 pattern = 1) : d201 pattern ≤ (1 : Int) + d14 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d201, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2479 pattern childGuard
    simpa only [d201, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d201, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d201, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2481 (pattern : Ten) (guard : d350 pattern = 1) : d206 pattern ≤ (1 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d206, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2480 pattern childGuard
    simpa only [d206, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d206, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d206, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2482 (pattern : Ten) (guard : d350 pattern = 1) : d210 pattern ≤ (1 : Int) + d27 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d210, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2481 pattern childGuard
    simpa only [d210, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d210, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1852 pattern childGuard
    simpa only [d210, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2483 (pattern : Ten) (guard : d350 pattern = 1) : d213 pattern ≤ (1 : Int) + d441 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d213, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2463 pattern childGuard
    simpa only [d213, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d213, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2482 pattern childGuard
    simpa only [d213, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2484 (pattern : Ten) (guard : d350 pattern = 1) : d216 pattern ≤ (1 : Int) + d442 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d216, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2463 pattern childGuard
    simpa only [d216, d442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d216, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2483 pattern childGuard
    simpa only [d216, d442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2485 (pattern : Ten) (guard : d350 pattern = 1) : d219 pattern ≤ (1 : Int) + d443 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d219, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2484 pattern childGuard
    simpa only [d219, d443, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d219, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2472 pattern childGuard
    simpa only [d219, d443, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2486 (pattern : Ten) (guard : d350 pattern = 1) : d220 pattern ≤ (1 : Int) + d444 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d220, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2475 pattern childGuard
    simpa only [d220, d444, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d220, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2485 pattern childGuard
    simpa only [d220, d444, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2487 (pattern : Ten) (guard : d447 pattern = 1) : d23 pattern ≤ (1 : Int) + d23 pattern := by
  omega
theorem c2488 (pattern : Ten) (guard : d447 pattern = 1) : d0 pattern ≤ (1 : Int) + d0 pattern := by
  omega
theorem c2489 (pattern : Ten) (guard : d360 pattern = 1) : d9 pattern ≤ (1 : Int) + d10 pattern := by
  change (9 : Int) ≤ (1 : Int) + 10
  decide
theorem c2490 (pattern : Ten) (guard : d446 pattern = 1) : d11 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d446, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2489 pattern childGuard
    simpa only [d446, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d446, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1913 pattern childGuard
    simpa only [d446, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2491 (pattern : Ten) (guard : d447 pattern = 1) : d11 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2490 pattern childGuard
    simpa only [d447, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1658 pattern childGuard
    simpa only [d447, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2492 (pattern : Ten) (guard : d447 pattern = 1) : d13 pattern ≤ (1 : Int) + d12 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2488 pattern childGuard
    simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2491 pattern childGuard
    simpa only [d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2493 (pattern : Ten) (guard : d447 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  omega
theorem c2494 (pattern : Ten) (guard : d447 pattern = 1) : d14 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2491 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2493 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2495 (pattern : Ten) (guard : d447 pattern = 1) : d19 pattern ≤ (1 : Int) + d18 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2492 pattern childGuard
    simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2494 pattern childGuard
    simpa only [d19, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2496 (pattern : Ten) (guard : d447 pattern = 1) : d20 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2494 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2493 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2497 (pattern : Ten) (guard : d447 pattern = 1) : d24 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2495 pattern childGuard
    simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2496 pattern childGuard
    simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2498 (pattern : Ten) (guard : d447 pattern = 1) : d29 pattern ≤ (1 : Int) + d408 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2487 pattern childGuard
    simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2497 pattern childGuard
    simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2499 (pattern : Ten) (guard : d447 pattern = 1) : d25 pattern ≤ (1 : Int) + d25 pattern := by
  omega
theorem c2500 (pattern : Ten) (guard : d447 pattern = 1) : d30 pattern ≤ (1 : Int) + d227 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2499 pattern childGuard
    simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2497 pattern childGuard
    simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2501 (pattern : Ten) (guard : d447 pattern = 1) : d33 pattern ≤ (1 : Int) + d409 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2498 pattern childGuard
    simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2500 pattern childGuard
    simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2502 (pattern : Ten) (guard : d447 pattern = 1) : d26 pattern ≤ (1 : Int) + d26 pattern := by
  omega
theorem c2503 (pattern : Ten) (guard : d447 pattern = 1) : d27 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2496 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2493 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2504 (pattern : Ten) (guard : d447 pattern = 1) : d31 pattern ≤ (1 : Int) + d228 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2502 pattern childGuard
    simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2503 pattern childGuard
    simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2505 (pattern : Ten) (guard : d447 pattern = 1) : d28 pattern ≤ (1 : Int) + d28 pattern := by
  omega
theorem c2506 (pattern : Ten) (guard : d447 pattern = 1) : d32 pattern ≤ (1 : Int) + d229 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2505 pattern childGuard
    simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2503 pattern childGuard
    simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2507 (pattern : Ten) (guard : d447 pattern = 1) : d34 pattern ≤ (1 : Int) + d231 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2504 pattern childGuard
    simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2506 pattern childGuard
    simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2508 (pattern : Ten) (guard : d447 pattern = 1) : d35 pattern ≤ (1 : Int) + d410 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2501 pattern childGuard
    simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2507 pattern childGuard
    simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2509 (pattern : Ten) (guard : d447 pattern = 1) : d36 pattern ≤ (1 : Int) + d233 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2507 pattern childGuard
    simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2493 pattern childGuard
    simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2510 (pattern : Ten) (guard : d447 pattern = 1) : d37 pattern ≤ (1 : Int) + d411 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2508 pattern childGuard
    simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2509 pattern childGuard
    simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2511 (pattern : Ten) (guard : d360 pattern = 1) : d0 pattern ≤ (1 : Int) + d1 pattern := by
  change (0 : Int) ≤ (1 : Int) + 1
  decide
theorem c2512 (pattern : Ten) (guard : d446 pattern = 1) : d171 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d446, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2511 pattern childGuard
    simpa only [d446, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d446, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1935 pattern childGuard
    simpa only [d446, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2513 (pattern : Ten) (guard : d446 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  omega
theorem c2514 (pattern : Ten) (guard : d446 pattern = 1) : d173 pattern ≤ (1 : Int) + d412 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d173, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2512 pattern childGuard
    simpa only [d173, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d173, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d173, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2515 (pattern : Ten) (guard : d446 pattern = 1) : d176 pattern ≤ (1 : Int) + d413 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d176, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2512 pattern childGuard
    simpa only [d176, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d176, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2514 pattern childGuard
    simpa only [d176, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2516 (pattern : Ten) (guard : d446 pattern = 1) : d177 pattern ≤ (1 : Int) + d414 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d177, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2514 pattern childGuard
    simpa only [d177, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d177, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d177, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2517 (pattern : Ten) (guard : d446 pattern = 1) : d180 pattern ≤ (1 : Int) + d415 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d180, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2515 pattern childGuard
    simpa only [d180, d415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d180, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2516 pattern childGuard
    simpa only [d180, d415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2518 (pattern : Ten) (guard : d446 pattern = 1) : d181 pattern ≤ (1 : Int) + d416 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d181, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2516 pattern childGuard
    simpa only [d181, d416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d181, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d181, d416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2519 (pattern : Ten) (guard : d446 pattern = 1) : d184 pattern ≤ (1 : Int) + d417 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d184, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2517 pattern childGuard
    simpa only [d184, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d184, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2518 pattern childGuard
    simpa only [d184, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2520 (pattern : Ten) (guard : d360 pattern = 1) : d2 pattern ≤ (1 : Int) + d3 pattern := by
  change (2 : Int) ≤ (1 : Int) + 3
  decide
theorem c2521 (pattern : Ten) (guard : d446 pattern = 1) : d172 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d446, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2520 pattern childGuard
    simpa only [d446, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d446, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1944 pattern childGuard
    simpa only [d446, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2522 (pattern : Ten) (guard : d446 pattern = 1) : d174 pattern ≤ (1 : Int) + d418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d174, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2512 pattern childGuard
    simpa only [d174, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d174, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2521 pattern childGuard
    simpa only [d174, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2523 (pattern : Ten) (guard : d446 pattern = 1) : d175 pattern ≤ (1 : Int) + d419 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d175, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2521 pattern childGuard
    simpa only [d175, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d175, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d175, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2524 (pattern : Ten) (guard : d446 pattern = 1) : d178 pattern ≤ (1 : Int) + d420 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d178, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2522 pattern childGuard
    simpa only [d178, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d178, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2523 pattern childGuard
    simpa only [d178, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2525 (pattern : Ten) (guard : d446 pattern = 1) : d179 pattern ≤ (1 : Int) + d421 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d179, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2523 pattern childGuard
    simpa only [d179, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d179, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d179, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2526 (pattern : Ten) (guard : d446 pattern = 1) : d182 pattern ≤ (1 : Int) + d422 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d182, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2524 pattern childGuard
    simpa only [d182, d422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d182, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2525 pattern childGuard
    simpa only [d182, d422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2527 (pattern : Ten) (guard : d446 pattern = 1) : d185 pattern ≤ (1 : Int) + d423 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d185, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2526 pattern childGuard
    simpa only [d185, d423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d185, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2518 pattern childGuard
    simpa only [d185, d423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2528 (pattern : Ten) (guard : d446 pattern = 1) : d188 pattern ≤ (1 : Int) + d424 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d188, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2519 pattern childGuard
    simpa only [d188, d424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d188, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2527 pattern childGuard
    simpa only [d188, d424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2529 (pattern : Ten) (guard : d446 pattern = 1) : d186 pattern ≤ (1 : Int) + d425 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d186, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2518 pattern childGuard
    simpa only [d186, d425, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d186, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d186, d425, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2530 (pattern : Ten) (guard : d446 pattern = 1) : d183 pattern ≤ (1 : Int) + d426 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d183, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2525 pattern childGuard
    simpa only [d183, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d183, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d183, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2531 (pattern : Ten) (guard : d446 pattern = 1) : d187 pattern ≤ (1 : Int) + d427 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d187, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2530 pattern childGuard
    simpa only [d187, d427, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d187, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d187, d427, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2532 (pattern : Ten) (guard : d446 pattern = 1) : d189 pattern ≤ (1 : Int) + d428 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d189, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2529 pattern childGuard
    simpa only [d189, d428, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d189, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2531 pattern childGuard
    simpa only [d189, d428, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2533 (pattern : Ten) (guard : d446 pattern = 1) : d190 pattern ≤ (1 : Int) + d429 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d190, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2528 pattern childGuard
    simpa only [d190, d429, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d190, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2532 pattern childGuard
    simpa only [d190, d429, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2534 (pattern : Ten) (guard : d446 pattern = 1) : d191 pattern ≤ (1 : Int) + d430 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d191, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2532 pattern childGuard
    simpa only [d191, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d191, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d191, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2535 (pattern : Ten) (guard : d446 pattern = 1) : d192 pattern ≤ (1 : Int) + d431 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d192, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2533 pattern childGuard
    simpa only [d192, d431, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d192, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2534 pattern childGuard
    simpa only [d192, d431, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2536 (pattern : Ten) (guard : d445 pattern = 1) : d37 pattern ≤ (0 : Int) + d37 pattern := by
  omega
theorem c2537 (pattern : Ten) (guard : d360 pattern = 1) : d192 pattern ≤ (0 : Int) + d192 pattern := by
  omega
theorem c2538 (pattern : Ten) (guard : d360 pattern = 1) : d0 pattern ≤ (1 : Int) + d0 pattern := by
  omega
theorem c2539 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (1 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2540 (pattern : Ten) (guard : d446 pattern = 1) : d0 pattern ≤ (1 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d446, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2538 pattern childGuard
    simpa only [d446, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d446, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2539 pattern childGuard
    simpa only [d446, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2541 (pattern : Ten) (guard : d447 pattern = 1) : d0 pattern ≤ (1 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2540 pattern childGuard
    simpa only [d447, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1850 pattern childGuard
    simpa only [d447, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2542 (pattern : Ten) (guard : d447 pattern = 1) : d12 pattern ≤ (1 : Int) + d173 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2541 pattern childGuard
    simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2493 pattern childGuard
    simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2543 (pattern : Ten) (guard : d447 pattern = 1) : d17 pattern ≤ (1 : Int) + d176 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2541 pattern childGuard
    simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2542 pattern childGuard
    simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2544 (pattern : Ten) (guard : d447 pattern = 1) : d18 pattern ≤ (1 : Int) + d177 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2542 pattern childGuard
    simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2493 pattern childGuard
    simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2545 (pattern : Ten) (guard : d447 pattern = 1) : d23 pattern ≤ (1 : Int) + d180 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2543 pattern childGuard
    simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2544 pattern childGuard
    simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2546 (pattern : Ten) (guard : d447 pattern = 1) : d9 pattern ≤ (1 : Int) + d10 pattern := by
  change (9 : Int) ≤ (1 : Int) + 10
  decide
theorem c2547 (pattern : Ten) (guard : d447 pattern = 1) : d67 pattern ≤ (1 : Int) + d173 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d67, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2541 pattern childGuard
    simpa only [d67, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d67, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2546 pattern childGuard
    simpa only [d67, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2548 (pattern : Ten) (guard : d447 pattern = 1) : d68 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2546 pattern childGuard
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2493 pattern childGuard
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2549 (pattern : Ten) (guard : d447 pattern = 1) : d69 pattern ≤ (1 : Int) + d177 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d69, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2547 pattern childGuard
    simpa only [d69, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d69, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2548 pattern childGuard
    simpa only [d69, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2550 (pattern : Ten) (guard : d447 pattern = 1) : d70 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2548 pattern childGuard
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2493 pattern childGuard
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2551 (pattern : Ten) (guard : d447 pattern = 1) : d71 pattern ≤ (1 : Int) + d181 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d71, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2549 pattern childGuard
    simpa only [d71, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d71, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2550 pattern childGuard
    simpa only [d71, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2552 (pattern : Ten) (guard : d447 pattern = 1) : d73 pattern ≤ (1 : Int) + d184 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d73, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2545 pattern childGuard
    simpa only [d73, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d73, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2551 pattern childGuard
    simpa only [d73, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2553 (pattern : Ten) (guard : d360 pattern = 1) : d2 pattern ≤ (1 : Int) + d2 pattern := by
  omega
theorem c2554 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (1 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2555 (pattern : Ten) (guard : d446 pattern = 1) : d2 pattern ≤ (1 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d446, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2553 pattern childGuard
    simpa only [d446, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d446, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2554 pattern childGuard
    simpa only [d446, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2556 (pattern : Ten) (guard : d447 pattern = 1) : d2 pattern ≤ (1 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2555 pattern childGuard
    simpa only [d447, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1869 pattern childGuard
    simpa only [d447, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2557 (pattern : Ten) (guard : d447 pattern = 1) : d15 pattern ≤ (1 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2541 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2556 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2558 (pattern : Ten) (guard : d447 pattern = 1) : d16 pattern ≤ (1 : Int) + d175 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2556 pattern childGuard
    simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2493 pattern childGuard
    simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2559 (pattern : Ten) (guard : d447 pattern = 1) : d21 pattern ≤ (1 : Int) + d178 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2557 pattern childGuard
    simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2558 pattern childGuard
    simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
