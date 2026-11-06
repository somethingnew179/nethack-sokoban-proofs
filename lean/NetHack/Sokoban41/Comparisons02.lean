/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons01
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c320 (pattern : Ten) (guard : d0 pattern = 1) : d11 pattern ≤ (0 : Int) + d195 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c321 (pattern : Ten) (guard : d350 pattern = 1) : d196 pattern ≤ (0 : Int) + d195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c319 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c320 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c322 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c323 (pattern : Ten) (guard : d350 pattern = 1) : d201 pattern ≤ (0 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d201, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c321 pattern childGuard
    simpa only [d201, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d201, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d201, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c324 (pattern : Ten) (guard : d350 pattern = 1) : d206 pattern ≤ (0 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d206, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c323 pattern childGuard
    simpa only [d206, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d206, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d206, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c325 (pattern : Ten) (guard : d350 pattern = 1) : d210 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d210, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c324 pattern childGuard
    simpa only [d210, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d210, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d210, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c326 (pattern : Ten) (guard : d350 pattern = 1) : d213 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c318 pattern childGuard
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c325 pattern childGuard
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c327 (pattern : Ten) (guard : d350 pattern = 1) : d216 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c318 pattern childGuard
    simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c326 pattern childGuard
    simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c328 (pattern : Ten) (guard : d350 pattern = 1) : d217 pattern ≤ (0 : Int) + d217 pattern := by
  omega
theorem c329 (pattern : Ten) (guard : d350 pattern = 1) : d219 pattern ≤ (0 : Int) + d299 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d219, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c327 pattern childGuard
    simpa only [d219, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d219, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d219, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c330 (pattern : Ten) (guard : d350 pattern = 1) : d220 pattern ≤ (0 : Int) + d300 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d220, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c317 pattern childGuard
    simpa only [d220, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d220, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c329 pattern childGuard
    simpa only [d220, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c331 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (0 : Int) + d56 pattern := by
  omega
theorem c332 (pattern : Ten) (guard : d367 pattern = 1) : d65 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d367, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c331 pattern childGuard
    simpa only [d367, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d367, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c216 pattern childGuard
    simpa only [d367, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c333 (pattern : Ten) (guard : d367 pattern = 1) : d66 pattern ≤ (0 : Int) + d135 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d367 pattern = 1 := by simpa only [d66, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c215 pattern childGuard
    simpa only [d66, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d367 pattern = 1 := by simpa only [d66, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c332 pattern childGuard
    simpa only [d66, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c334 (pattern : Ten) (guard : d381 pattern = 1) : d207 pattern ≤ (0 : Int) + d207 pattern := by
  omega
theorem c335 (pattern : Ten) (guard : d382 pattern = 1) : d218 pattern ≤ (0 : Int) + d290 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d381 pattern = 1 := by simpa only [d382, d218, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c334 pattern childGuard
    simpa only [d382, d218, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d382, d218, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c219 pattern childGuard
    simpa only [d382, d218, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c336 (pattern : Ten) (guard : d381 pattern = 1) : d216 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d381, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d381, d216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d381, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c326 pattern childGuard
    simpa only [d381, d216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c337 (pattern : Ten) (guard : d382 pattern = 1) : d219 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d381 pattern = 1 := by simpa only [d382, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c336 pattern childGuard
    simpa only [d382, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d382, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c221 pattern childGuard
    simpa only [d382, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c338 (pattern : Ten) (guard : d382 pattern = 1) : d220 pattern ≤ (0 : Int) + d291 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d382 pattern = 1 := by simpa only [d220, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c335 pattern childGuard
    simpa only [d220, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d382 pattern = 1 := by simpa only [d220, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c337 pattern childGuard
    simpa only [d220, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c339 (pattern : Ten) (guard : d358 pattern = 1) : d11 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d358, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c158 pattern childGuard
    simpa only [d358, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d358, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5 pattern childGuard
    simpa only [d358, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c340 (pattern : Ten) (guard : d359 pattern = 1) : d11 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c339 pattern childGuard
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7 pattern childGuard
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c341 (pattern : Ten) (guard : d359 pattern = 1) : d13 pattern ≤ (0 : Int) + d67 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c157 pattern childGuard
    simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c340 pattern childGuard
    simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c342 (pattern : Ten) (guard : d359 pattern = 1) : d14 pattern ≤ (0 : Int) + d68 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c340 pattern childGuard
    simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c162 pattern childGuard
    simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c343 (pattern : Ten) (guard : d359 pattern = 1) : d19 pattern ≤ (0 : Int) + d69 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c341 pattern childGuard
    simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c342 pattern childGuard
    simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c344 (pattern : Ten) (guard : d359 pattern = 1) : d20 pattern ≤ (0 : Int) + d70 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c342 pattern childGuard
    simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c162 pattern childGuard
    simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c345 (pattern : Ten) (guard : d359 pattern = 1) : d24 pattern ≤ (0 : Int) + d71 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c343 pattern childGuard
    simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c344 pattern childGuard
    simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c346 (pattern : Ten) (guard : d359 pattern = 1) : d29 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c156 pattern childGuard
    simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c345 pattern childGuard
    simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c347 (pattern : Ten) (guard : d359 pattern = 1) : d30 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c168 pattern childGuard
    simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c345 pattern childGuard
    simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c348 (pattern : Ten) (guard : d359 pattern = 1) : d33 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c346 pattern childGuard
    simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c347 pattern childGuard
    simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c349 (pattern : Ten) (guard : d359 pattern = 1) : d27 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c344 pattern childGuard
    simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c162 pattern childGuard
    simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c350 (pattern : Ten) (guard : d359 pattern = 1) : d31 pattern ≤ (0 : Int) + d75 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c171 pattern childGuard
    simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c349 pattern childGuard
    simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c351 (pattern : Ten) (guard : d359 pattern = 1) : d32 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c174 pattern childGuard
    simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c349 pattern childGuard
    simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c352 (pattern : Ten) (guard : d359 pattern = 1) : d34 pattern ≤ (0 : Int) + d78 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c350 pattern childGuard
    simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c351 pattern childGuard
    simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c353 (pattern : Ten) (guard : d359 pattern = 1) : d35 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c348 pattern childGuard
    simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c352 pattern childGuard
    simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c354 (pattern : Ten) (guard : d359 pattern = 1) : d36 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c352 pattern childGuard
    simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c162 pattern childGuard
    simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c355 (pattern : Ten) (guard : d359 pattern = 1) : d37 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c353 pattern childGuard
    simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c354 pattern childGuard
    simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c356 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c357 (pattern : Ten) (guard : d356 pattern = 1) : d239 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d356, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c28 pattern childGuard
    simpa only [d356, d239, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d356, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d356, d239, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c358 (pattern : Ten) (guard : d358 pattern = 1) : d240 pattern ≤ (0 : Int) + d221 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d358, d240, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c357 pattern childGuard
    simpa only [d358, d240, d221, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d358, d240, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c29 pattern childGuard
    simpa only [d358, d240, d221, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c359 (pattern : Ten) (guard : d358 pattern = 1) : d171 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d358, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c181 pattern childGuard
    simpa only [d358, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d358, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c31 pattern childGuard
    simpa only [d358, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c360 (pattern : Ten) (guard : d358 pattern = 1) : d241 pattern ≤ (0 : Int) + d222 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d241, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c358 pattern childGuard
    simpa only [d241, d222, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d241, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c359 pattern childGuard
    simpa only [d241, d222, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c361 (pattern : Ten) (guard : d358 pattern = 1) : d242 pattern ≤ (0 : Int) + d223 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d242, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c360 pattern childGuard
    simpa only [d242, d223, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d242, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c359 pattern childGuard
    simpa only [d242, d223, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c362 (pattern : Ten) (guard : d358 pattern = 1) : d173 pattern ≤ (0 : Int) + d12 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c359 pattern childGuard
    simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c363 (pattern : Ten) (guard : d358 pattern = 1) : d243 pattern ≤ (0 : Int) + d224 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d243, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c361 pattern childGuard
    simpa only [d243, d224, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d243, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c362 pattern childGuard
    simpa only [d243, d224, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c364 (pattern : Ten) (guard : d358 pattern = 1) : d177 pattern ≤ (0 : Int) + d18 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c362 pattern childGuard
    simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c365 (pattern : Ten) (guard : d358 pattern = 1) : d244 pattern ≤ (0 : Int) + d225 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d244, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c363 pattern childGuard
    simpa only [d244, d225, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d244, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c364 pattern childGuard
    simpa only [d244, d225, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c366 (pattern : Ten) (guard : d358 pattern = 1) : d181 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c364 pattern childGuard
    simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c367 (pattern : Ten) (guard : d358 pattern = 1) : d245 pattern ≤ (0 : Int) + d226 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d245, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c365 pattern childGuard
    simpa only [d245, d226, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d245, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c366 pattern childGuard
    simpa only [d245, d226, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c368 (pattern : Ten) (guard : d358 pattern = 1) : d172 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d358, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c192 pattern childGuard
    simpa only [d358, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d358, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c43 pattern childGuard
    simpa only [d358, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c369 (pattern : Ten) (guard : d358 pattern = 1) : d174 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c359 pattern childGuard
    simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c368 pattern childGuard
    simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c370 (pattern : Ten) (guard : d358 pattern = 1) : d175 pattern ≤ (0 : Int) + d16 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c368 pattern childGuard
    simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c371 (pattern : Ten) (guard : d358 pattern = 1) : d178 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c369 pattern childGuard
    simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c370 pattern childGuard
    simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c372 (pattern : Ten) (guard : d358 pattern = 1) : d179 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c370 pattern childGuard
    simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c373 (pattern : Ten) (guard : d358 pattern = 1) : d182 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c371 pattern childGuard
    simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c372 pattern childGuard
    simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c374 (pattern : Ten) (guard : d358 pattern = 1) : d185 pattern ≤ (0 : Int) + d227 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c373 pattern childGuard
    simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c366 pattern childGuard
    simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c375 (pattern : Ten) (guard : d358 pattern = 1) : d246 pattern ≤ (0 : Int) + d230 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d246, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c367 pattern childGuard
    simpa only [d246, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d246, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c374 pattern childGuard
    simpa only [d246, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c376 (pattern : Ten) (guard : d358 pattern = 1) : d186 pattern ≤ (0 : Int) + d228 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c366 pattern childGuard
    simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c377 (pattern : Ten) (guard : d358 pattern = 1) : d183 pattern ≤ (0 : Int) + d28 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c372 pattern childGuard
    simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c378 (pattern : Ten) (guard : d358 pattern = 1) : d187 pattern ≤ (0 : Int) + d229 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c377 pattern childGuard
    simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c379 (pattern : Ten) (guard : d358 pattern = 1) : d189 pattern ≤ (0 : Int) + d231 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c376 pattern childGuard
    simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c378 pattern childGuard
    simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c380 (pattern : Ten) (guard : d358 pattern = 1) : d247 pattern ≤ (0 : Int) + d232 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d247, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c375 pattern childGuard
    simpa only [d247, d232, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d247, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c379 pattern childGuard
    simpa only [d247, d232, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c381 (pattern : Ten) (guard : d358 pattern = 1) : d191 pattern ≤ (0 : Int) + d233 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c379 pattern childGuard
    simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c382 (pattern : Ten) (guard : d358 pattern = 1) : d248 pattern ≤ (0 : Int) + d234 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d248, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c380 pattern childGuard
    simpa only [d248, d234, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d248, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c381 pattern childGuard
    simpa only [d248, d234, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c383 (pattern : Ten) (guard : d356 pattern = 1) : d240 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d240, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c357 pattern childGuard
    simpa only [d240, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d240, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d240, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c384 (pattern : Ten) (guard : d356 pattern = 1) : d241 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c383 pattern childGuard
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c94 pattern childGuard
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c385 (pattern : Ten) (guard : d356 pattern = 1) : d242 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c384 pattern childGuard
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c94 pattern childGuard
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c386 (pattern : Ten) (guard : d356 pattern = 1) : d243 pattern ≤ (0 : Int) + d176 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d243, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c385 pattern childGuard
    simpa only [d243, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d243, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c97 pattern childGuard
    simpa only [d243, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c387 (pattern : Ten) (guard : d356 pattern = 1) : d244 pattern ≤ (0 : Int) + d180 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d244, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c386 pattern childGuard
    simpa only [d244, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d244, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c99 pattern childGuard
    simpa only [d244, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c388 (pattern : Ten) (guard : d356 pattern = 1) : d245 pattern ≤ (0 : Int) + d184 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d245, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c387 pattern childGuard
    simpa only [d245, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d245, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c101 pattern childGuard
    simpa only [d245, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c389 (pattern : Ten) (guard : d356 pattern = 1) : d246 pattern ≤ (0 : Int) + d188 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d246, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c388 pattern childGuard
    simpa only [d246, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d246, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c103 pattern childGuard
    simpa only [d246, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c390 (pattern : Ten) (guard : d356 pattern = 1) : d247 pattern ≤ (0 : Int) + d190 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d247, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c389 pattern childGuard
    simpa only [d247, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d247, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c105 pattern childGuard
    simpa only [d247, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c391 (pattern : Ten) (guard : d356 pattern = 1) : d248 pattern ≤ (0 : Int) + d192 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d248, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c390 pattern childGuard
    simpa only [d248, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d248, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c107 pattern childGuard
    simpa only [d248, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c392 (pattern : Ten) (guard : d356 pattern = 1) : d192 pattern ≤ (0 : Int) + d192 pattern := by
  omega
theorem c393 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c394 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c395 (pattern : Ten) (guard : d384 pattern = 1) : d0 pattern ≤ (0 : Int) + d86 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c394 pattern childGuard
    simpa only [d384, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c396 (pattern : Ten) (guard : d384 pattern = 1) : d12 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c397 (pattern : Ten) (guard : d384 pattern = 1) : d17 pattern ≤ (0 : Int) + d87 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d17, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c395 pattern childGuard
    simpa only [d17, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d17, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c396 pattern childGuard
    simpa only [d17, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c398 (pattern : Ten) (guard : d384 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c399 (pattern : Ten) (guard : d384 pattern = 1) : d18 pattern ≤ (0 : Int) + d88 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d18, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c396 pattern childGuard
    simpa only [d18, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d18, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d18, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c400 (pattern : Ten) (guard : d384 pattern = 1) : d23 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d23, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c397 pattern childGuard
    simpa only [d23, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d23, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c399 pattern childGuard
    simpa only [d23, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c401 (pattern : Ten) (guard : d0 pattern = 1) : d11 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c402 (pattern : Ten) (guard : d384 pattern = 1) : d13 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c401 pattern childGuard
    simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c403 (pattern : Ten) (guard : d350 pattern = 1) : d11 pattern ≤ (0 : Int) + d11 pattern := by
  omega
theorem c404 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c405 (pattern : Ten) (guard : d384 pattern = 1) : d14 pattern ≤ (0 : Int) + d11 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c403 pattern childGuard
    simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c404 pattern childGuard
    simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c406 (pattern : Ten) (guard : d384 pattern = 1) : d19 pattern ≤ (0 : Int) + d89 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d19, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c402 pattern childGuard
    simpa only [d19, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d19, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c405 pattern childGuard
    simpa only [d19, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c407 (pattern : Ten) (guard : d384 pattern = 1) : d20 pattern ≤ (0 : Int) + d90 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d20, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c405 pattern childGuard
    simpa only [d20, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d20, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d20, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c408 (pattern : Ten) (guard : d384 pattern = 1) : d24 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d24, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c406 pattern childGuard
    simpa only [d24, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d24, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c407 pattern childGuard
    simpa only [d24, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c409 (pattern : Ten) (guard : d384 pattern = 1) : d29 pattern ≤ (0 : Int) + d99 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d29, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c400 pattern childGuard
    simpa only [d29, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d29, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c408 pattern childGuard
    simpa only [d29, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c410 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c411 (pattern : Ten) (guard : d384 pattern = 1) : d15 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c410 pattern childGuard
    simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c412 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (0 : Int) + d2 pattern := by
  omega
theorem c413 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c414 (pattern : Ten) (guard : d384 pattern = 1) : d16 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c412 pattern childGuard
    simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c413 pattern childGuard
    simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c415 (pattern : Ten) (guard : d384 pattern = 1) : d21 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d21, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c411 pattern childGuard
    simpa only [d21, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d21, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c414 pattern childGuard
    simpa only [d21, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c416 (pattern : Ten) (guard : d384 pattern = 1) : d22 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d22, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c414 pattern childGuard
    simpa only [d22, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d22, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d22, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c417 (pattern : Ten) (guard : d384 pattern = 1) : d25 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d25, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c415 pattern childGuard
    simpa only [d25, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d25, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c416 pattern childGuard
    simpa only [d25, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c418 (pattern : Ten) (guard : d384 pattern = 1) : d30 pattern ≤ (0 : Int) + d100 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d30, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c417 pattern childGuard
    simpa only [d30, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d30, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c408 pattern childGuard
    simpa only [d30, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c419 (pattern : Ten) (guard : d384 pattern = 1) : d33 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d33, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c409 pattern childGuard
    simpa only [d33, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d33, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c418 pattern childGuard
    simpa only [d33, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c420 (pattern : Ten) (guard : d384 pattern = 1) : d26 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d26, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c399 pattern childGuard
    simpa only [d26, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d26, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d26, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c421 (pattern : Ten) (guard : d384 pattern = 1) : d27 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d27, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c407 pattern childGuard
    simpa only [d27, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d27, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d27, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c422 (pattern : Ten) (guard : d384 pattern = 1) : d31 pattern ≤ (0 : Int) + d101 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d31, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c420 pattern childGuard
    simpa only [d31, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d31, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c421 pattern childGuard
    simpa only [d31, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c423 (pattern : Ten) (guard : d384 pattern = 1) : d28 pattern ≤ (0 : Int) + d98 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d28, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c416 pattern childGuard
    simpa only [d28, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d28, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d28, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c424 (pattern : Ten) (guard : d384 pattern = 1) : d32 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d32, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c423 pattern childGuard
    simpa only [d32, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d32, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c421 pattern childGuard
    simpa only [d32, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c425 (pattern : Ten) (guard : d384 pattern = 1) : d34 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d34, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c422 pattern childGuard
    simpa only [d34, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d34, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c424 pattern childGuard
    simpa only [d34, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c426 (pattern : Ten) (guard : d384 pattern = 1) : d35 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d35, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c419 pattern childGuard
    simpa only [d35, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d35, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c425 pattern childGuard
    simpa only [d35, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c427 (pattern : Ten) (guard : d384 pattern = 1) : d36 pattern ≤ (0 : Int) + d106 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d36, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c425 pattern childGuard
    simpa only [d36, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d36, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d36, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c428 (pattern : Ten) (guard : d384 pattern = 1) : d37 pattern ≤ (0 : Int) + d107 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d37, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c426 pattern childGuard
    simpa only [d37, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d37, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c427 pattern childGuard
    simpa only [d37, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c429 (pattern : Ten) (guard : d0 pattern = 1) : d171 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c430 (pattern : Ten) (guard : d383 pattern = 1) : d171 pattern ≤ (0 : Int) + d173 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c291 pattern childGuard
    simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c429 pattern childGuard
    simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c431 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c432 (pattern : Ten) (guard : d383 pattern = 1) : d173 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c291 pattern childGuard
    simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c431 pattern childGuard
    simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c433 (pattern : Ten) (guard : d383 pattern = 1) : d176 pattern ≤ (0 : Int) + d249 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d176, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c430 pattern childGuard
    simpa only [d176, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d176, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c432 pattern childGuard
    simpa only [d176, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c434 (pattern : Ten) (guard : d383 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c435 (pattern : Ten) (guard : d383 pattern = 1) : d177 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d177, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c432 pattern childGuard
    simpa only [d177, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d177, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d177, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c436 (pattern : Ten) (guard : d383 pattern = 1) : d180 pattern ≤ (0 : Int) + d253 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d180, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c433 pattern childGuard
    simpa only [d180, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d180, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c435 pattern childGuard
    simpa only [d180, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c437 (pattern : Ten) (guard : d383 pattern = 1) : d181 pattern ≤ (0 : Int) + d254 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d181, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c435 pattern childGuard
    simpa only [d181, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d181, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d181, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c438 (pattern : Ten) (guard : d383 pattern = 1) : d184 pattern ≤ (0 : Int) + d257 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d184, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c436 pattern childGuard
    simpa only [d184, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d184, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c437 pattern childGuard
    simpa only [d184, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c439 (pattern : Ten) (guard : d0 pattern = 1) : d172 pattern ≤ (0 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c440 (pattern : Ten) (guard : d383 pattern = 1) : d174 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c291 pattern childGuard
    simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c439 pattern childGuard
    simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c441 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (0 : Int) + d172 pattern := by
  omega
theorem c442 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c443 (pattern : Ten) (guard : d383 pattern = 1) : d175 pattern ≤ (0 : Int) + d172 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c441 pattern childGuard
    simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c442 pattern childGuard
    simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c444 (pattern : Ten) (guard : d383 pattern = 1) : d178 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d178, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c440 pattern childGuard
    simpa only [d178, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d178, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c443 pattern childGuard
    simpa only [d178, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c445 (pattern : Ten) (guard : d383 pattern = 1) : d179 pattern ≤ (0 : Int) + d252 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d179, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c443 pattern childGuard
    simpa only [d179, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d179, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d179, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c446 (pattern : Ten) (guard : d383 pattern = 1) : d182 pattern ≤ (0 : Int) + d255 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d182, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c444 pattern childGuard
    simpa only [d182, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d182, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d182, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c447 (pattern : Ten) (guard : d383 pattern = 1) : d185 pattern ≤ (0 : Int) + d258 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d185, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c446 pattern childGuard
    simpa only [d185, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d185, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c437 pattern childGuard
    simpa only [d185, d258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c448 (pattern : Ten) (guard : d383 pattern = 1) : d188 pattern ≤ (0 : Int) + d261 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d188, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c438 pattern childGuard
    simpa only [d188, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d188, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c447 pattern childGuard
    simpa only [d188, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c449 (pattern : Ten) (guard : d383 pattern = 1) : d186 pattern ≤ (0 : Int) + d259 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d186, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c437 pattern childGuard
    simpa only [d186, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d186, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d186, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c450 (pattern : Ten) (guard : d383 pattern = 1) : d183 pattern ≤ (0 : Int) + d256 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d183, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d183, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d183, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d183, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c451 (pattern : Ten) (guard : d383 pattern = 1) : d187 pattern ≤ (0 : Int) + d260 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d187, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c450 pattern childGuard
    simpa only [d187, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d187, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d187, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c452 (pattern : Ten) (guard : d383 pattern = 1) : d189 pattern ≤ (0 : Int) + d262 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d189, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c449 pattern childGuard
    simpa only [d189, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d189, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c451 pattern childGuard
    simpa only [d189, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c453 (pattern : Ten) (guard : d383 pattern = 1) : d190 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d190, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c448 pattern childGuard
    simpa only [d190, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d190, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c452 pattern childGuard
    simpa only [d190, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c454 (pattern : Ten) (guard : d383 pattern = 1) : d191 pattern ≤ (0 : Int) + d264 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d191, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c452 pattern childGuard
    simpa only [d191, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d191, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d191, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c455 (pattern : Ten) (guard : d383 pattern = 1) : d192 pattern ≤ (0 : Int) + d265 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d192, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c453 pattern childGuard
    simpa only [d192, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d192, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c454 pattern childGuard
    simpa only [d192, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c456 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d137 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c457 (pattern : Ten) (guard : d384 pattern = 1) : d0 pattern ≤ (0 : Int) + d138 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c456 pattern childGuard
    simpa only [d384, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c458 (pattern : Ten) (guard : d384 pattern = 1) : d12 pattern ≤ (0 : Int) + d12 pattern := by
  omega
theorem c459 (pattern : Ten) (guard : d384 pattern = 1) : d17 pattern ≤ (0 : Int) + d139 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d17, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c457 pattern childGuard
    simpa only [d17, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d17, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c458 pattern childGuard
    simpa only [d17, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c460 (pattern : Ten) (guard : d384 pattern = 1) : d18 pattern ≤ (0 : Int) + d18 pattern := by
  omega
theorem c461 (pattern : Ten) (guard : d384 pattern = 1) : d23 pattern ≤ (0 : Int) + d142 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d23, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c459 pattern childGuard
    simpa only [d23, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d23, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c460 pattern childGuard
    simpa only [d23, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c462 (pattern : Ten) (guard : d0 pattern = 1) : d11 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c463 (pattern : Ten) (guard : d384 pattern = 1) : d13 pattern ≤ (0 : Int) + d12 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c462 pattern childGuard
    simpa only [d384, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c464 (pattern : Ten) (guard : d384 pattern = 1) : d14 pattern ≤ (0 : Int) + d14 pattern := by
  omega
theorem c465 (pattern : Ten) (guard : d384 pattern = 1) : d19 pattern ≤ (0 : Int) + d140 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d19, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c463 pattern childGuard
    simpa only [d19, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d19, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c464 pattern childGuard
    simpa only [d19, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c466 (pattern : Ten) (guard : d384 pattern = 1) : d20 pattern ≤ (0 : Int) + d20 pattern := by
  omega
theorem c467 (pattern : Ten) (guard : d384 pattern = 1) : d24 pattern ≤ (0 : Int) + d143 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d24, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c465 pattern childGuard
    simpa only [d24, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d24, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c466 pattern childGuard
    simpa only [d24, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c468 (pattern : Ten) (guard : d384 pattern = 1) : d29 pattern ≤ (0 : Int) + d145 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d29, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c461 pattern childGuard
    simpa only [d29, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d29, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c467 pattern childGuard
    simpa only [d29, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c469 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c470 (pattern : Ten) (guard : d384 pattern = 1) : d15 pattern ≤ (0 : Int) + d12 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d384, d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c469 pattern childGuard
    simpa only [d384, d15, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c471 (pattern : Ten) (guard : d384 pattern = 1) : d16 pattern ≤ (0 : Int) + d16 pattern := by
  omega
theorem c472 (pattern : Ten) (guard : d384 pattern = 1) : d21 pattern ≤ (0 : Int) + d141 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d21, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c470 pattern childGuard
    simpa only [d21, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d21, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c471 pattern childGuard
    simpa only [d21, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c473 (pattern : Ten) (guard : d384 pattern = 1) : d22 pattern ≤ (0 : Int) + d22 pattern := by
  omega
theorem c474 (pattern : Ten) (guard : d384 pattern = 1) : d25 pattern ≤ (0 : Int) + d144 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d25, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c472 pattern childGuard
    simpa only [d25, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d25, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c473 pattern childGuard
    simpa only [d25, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c475 (pattern : Ten) (guard : d384 pattern = 1) : d30 pattern ≤ (0 : Int) + d146 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d30, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c474 pattern childGuard
    simpa only [d30, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d30, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c467 pattern childGuard
    simpa only [d30, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c476 (pattern : Ten) (guard : d384 pattern = 1) : d33 pattern ≤ (0 : Int) + d147 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d33, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c468 pattern childGuard
    simpa only [d33, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d33, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c475 pattern childGuard
    simpa only [d33, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c477 (pattern : Ten) (guard : d384 pattern = 1) : d34 pattern ≤ (0 : Int) + d34 pattern := by
  omega
theorem c478 (pattern : Ten) (guard : d384 pattern = 1) : d35 pattern ≤ (0 : Int) + d148 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d35, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c476 pattern childGuard
    simpa only [d35, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d35, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c477 pattern childGuard
    simpa only [d35, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c479 (pattern : Ten) (guard : d384 pattern = 1) : d36 pattern ≤ (0 : Int) + d36 pattern := by
  omega
end NetHack.Sokoban41.Diagram
