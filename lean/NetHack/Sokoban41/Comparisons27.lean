/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons26
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c4320 (pattern : Ten) (guard : d350 pattern = 1) : d163 pattern ≤ (12 : Int) + d334 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4305 pattern childGuard
    simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4321 (pattern : Ten) (guard : d350 pattern = 1) : d166 pattern ≤ (12 : Int) + d336 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4319 pattern childGuard
    simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4320 pattern childGuard
    simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4322 (pattern : Ten) (guard : d350 pattern = 1) : d168 pattern ≤ (12 : Int) + d347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4311 pattern childGuard
    simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4321 pattern childGuard
    simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4323 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (12 : Int) + d8 pattern := by
  change (7 : Int) ≤ (12 : Int) + 8
  decide
theorem c4324 (pattern : Ten) (guard : d1 pattern = 1) : d38 pattern ≤ (12 : Int) + d8 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4323 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4298 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4325 (pattern : Ten) (guard : d1 pattern = 1) : d40 pattern ≤ (12 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4324 pattern childGuard
    simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4299 pattern childGuard
    simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4326 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (12 : Int) + d195 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4327 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (12 : Int) + d195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4325 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4326 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4328 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (12 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4327 pattern childGuard
    simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4329 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (12 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4328 pattern childGuard
    simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4330 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (12 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4329 pattern childGuard
    simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4331 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (12 : Int) + d10 pattern := by
  change (9 : Int) ≤ (12 : Int) + 10
  decide
theorem c4332 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (12 : Int) + d10 pattern := by
  omega
theorem c4333 (pattern : Ten) (guard : d1 pattern = 1) : d39 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4331 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4334 (pattern : Ten) (guard : d1 pattern = 1) : d41 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4333 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4335 (pattern : Ten) (guard : d0 pattern = 1) : d41 pattern ≤ (12 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4336 (pattern : Ten) (guard : d350 pattern = 1) : d41 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4334 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4335 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4337 (pattern : Ten) (guard : d350 pattern = 1) : d47 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4336 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4338 (pattern : Ten) (guard : d350 pattern = 1) : d53 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4337 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4339 (pattern : Ten) (guard : d350 pattern = 1) : d57 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4338 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4340 (pattern : Ten) (guard : d350 pattern = 1) : d164 pattern ≤ (12 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4330 pattern childGuard
    simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4339 pattern childGuard
    simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4341 (pattern : Ten) (guard : d350 pattern = 1) : d60 pattern ≤ (12 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4330 pattern childGuard
    simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4342 (pattern : Ten) (guard : d350 pattern = 1) : d167 pattern ≤ (12 : Int) + d214 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4340 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4341 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4343 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (12 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4344 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (12 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4325 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4343 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4345 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (12 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4344 pattern childGuard
    simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4346 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (12 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4345 pattern childGuard
    simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4347 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (12 : Int) + d210 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4346 pattern childGuard
    simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4348 (pattern : Ten) (guard : d350 pattern = 1) : d60 pattern ≤ (12 : Int) + d335 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4347 pattern childGuard
    simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4349 (pattern : Ten) (guard : d350 pattern = 1) : d61 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4339 pattern childGuard
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4350 (pattern : Ten) (guard : d350 pattern = 1) : d63 pattern ≤ (12 : Int) + d337 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4348 pattern childGuard
    simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4349 pattern childGuard
    simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4351 (pattern : Ten) (guard : d350 pattern = 1) : d169 pattern ≤ (12 : Int) + d348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4342 pattern childGuard
    simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4350 pattern childGuard
    simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4352 (pattern : Ten) (guard : d350 pattern = 1) : d170 pattern ≤ (12 : Int) + d349 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4322 pattern childGuard
    simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4351 pattern childGuard
    simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4353 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (12 : Int) + d10 pattern := by
  change (0 : Int) ≤ (12 : Int) + 10
  decide
theorem c4354 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (12 : Int) + d10 pattern := by
  change (1 : Int) ≤ (12 : Int) + 10
  decide
theorem c4355 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4353 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4354 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4356 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (12 : Int) + d10 pattern := by
  change (2 : Int) ≤ (12 : Int) + 10
  decide
theorem c4357 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (12 : Int) + d10 pattern := by
  change (3 : Int) ≤ (12 : Int) + 10
  decide
theorem c4358 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4356 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4357 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4359 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4355 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4358 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4360 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (12 : Int) + d10 pattern := by
  change (4 : Int) ≤ (12 : Int) + 10
  decide
theorem c4361 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (12 : Int) + d10 pattern := by
  change (5 : Int) ≤ (12 : Int) + 10
  decide
theorem c4362 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4360 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4361 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4363 (pattern : Ten) (guard : d1 pattern = 1) : d197 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4362 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4364 (pattern : Ten) (guard : d1 pattern = 1) : d202 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4359 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4363 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4365 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (12 : Int) + d10 pattern := by
  change (6 : Int) ≤ (12 : Int) + 10
  decide
theorem c4366 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (12 : Int) + d10 pattern := by
  change (7 : Int) ≤ (12 : Int) + 10
  decide
theorem c4367 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4365 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4366 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4368 (pattern : Ten) (guard : d1 pattern = 1) : d198 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4367 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4369 (pattern : Ten) (guard : d1 pattern = 1) : d203 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4368 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4370 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4364 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4369 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4371 (pattern : Ten) (guard : d1 pattern = 1) : d310 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4357 pattern childGuard
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4360 pattern childGuard
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4372 (pattern : Ten) (guard : d1 pattern = 1) : d314 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4358 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4371 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4373 (pattern : Ten) (guard : d1 pattern = 1) : d311 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4361 pattern childGuard
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4365 pattern childGuard
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4374 (pattern : Ten) (guard : d1 pattern = 1) : d315 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4362 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4373 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4375 (pattern : Ten) (guard : d1 pattern = 1) : d320 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4372 pattern childGuard
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4374 pattern childGuard
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4376 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (12 : Int) + d10 pattern := by
  change (8 : Int) ≤ (12 : Int) + 10
  decide
theorem c4377 (pattern : Ten) (guard : d1 pattern = 1) : d312 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4366 pattern childGuard
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4376 pattern childGuard
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4378 (pattern : Ten) (guard : d1 pattern = 1) : d316 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4367 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4377 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4379 (pattern : Ten) (guard : d1 pattern = 1) : d319 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4378 pattern childGuard
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4380 (pattern : Ten) (guard : d1 pattern = 1) : d323 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4375 pattern childGuard
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4379 pattern childGuard
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4381 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4376 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4331 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4382 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4331 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4383 (pattern : Ten) (guard : d1 pattern = 1) : d196 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4381 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4382 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4384 (pattern : Ten) (guard : d1 pattern = 1) : d201 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4383 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4385 (pattern : Ten) (guard : d1 pattern = 1) : d206 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4384 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4386 (pattern : Ten) (guard : d1 pattern = 1) : d325 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4380 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4385 pattern childGuard
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4387 (pattern : Ten) (guard : d1 pattern = 1) : d344 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4370 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4386 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4388 (pattern : Ten) (guard : d1 pattern = 1) : d341 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4374 pattern childGuard
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4378 pattern childGuard
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4389 (pattern : Ten) (guard : d1 pattern = 1) : d342 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4388 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4384 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4390 (pattern : Ten) (guard : d1 pattern = 1) : d343 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4389 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4391 (pattern : Ten) (guard : d1 pattern = 1) : d345 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4370 pattern childGuard
    simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4390 pattern childGuard
    simpa only [d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4392 (pattern : Ten) (guard : d1 pattern = 1) : d346 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4387 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4391 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4393 (pattern : Ten) (guard : d1 pattern = 1) : d309 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4354 pattern childGuard
    simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4356 pattern childGuard
    simpa only [d309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4394 (pattern : Ten) (guard : d1 pattern = 1) : d313 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4355 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4393 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4395 (pattern : Ten) (guard : d1 pattern = 1) : d317 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4394 pattern childGuard
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4372 pattern childGuard
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4396 (pattern : Ten) (guard : d1 pattern = 1) : d318 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4374 pattern childGuard
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4397 (pattern : Ten) (guard : d1 pattern = 1) : d321 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4395 pattern childGuard
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4396 pattern childGuard
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4398 (pattern : Ten) (guard : d1 pattern = 1) : d322 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4379 pattern childGuard
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4399 (pattern : Ten) (guard : d1 pattern = 1) : d324 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4397 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4398 pattern childGuard
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4400 (pattern : Ten) (guard : d1 pattern = 1) : d333 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4399 pattern childGuard
    simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4401 (pattern : Ten) (guard : d1 pattern = 1) : d334 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4386 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4402 (pattern : Ten) (guard : d1 pattern = 1) : d336 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4400 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4401 pattern childGuard
    simpa only [d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4403 (pattern : Ten) (guard : d1 pattern = 1) : d347 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4392 pattern childGuard
    simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4402 pattern childGuard
    simpa only [d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4404 (pattern : Ten) (guard : d1 pattern = 1) : d200 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4381 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4405 (pattern : Ten) (guard : d1 pattern = 1) : d205 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4404 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4406 (pattern : Ten) (guard : d1 pattern = 1) : d209 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4405 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4407 (pattern : Ten) (guard : d1 pattern = 1) : d214 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4406 pattern childGuard
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4408 (pattern : Ten) (guard : d1 pattern = 1) : d210 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4385 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4409 (pattern : Ten) (guard : d1 pattern = 1) : d335 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4408 pattern childGuard
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4410 (pattern : Ten) (guard : d1 pattern = 1) : d337 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4409 pattern childGuard
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4411 (pattern : Ten) (guard : d1 pattern = 1) : d348 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4407 pattern childGuard
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4410 pattern childGuard
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4412 (pattern : Ten) (guard : d1 pattern = 1) : d349 pattern ≤ (12 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4403 pattern childGuard
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4411 pattern childGuard
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4413 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (13 : Int) + d0 pattern := by
  omega
theorem c4414 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (13 : Int) + d1 pattern := by
  change (0 : Int) ≤ (13 : Int) + 1
  decide
theorem c4415 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (13 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4413 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4414 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4416 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (13 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4417 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (13 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4415 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4416 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4418 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (13 : Int) + d2 pattern := by
  omega
theorem c4419 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (13 : Int) + d3 pattern := by
  change (2 : Int) ≤ (13 : Int) + 3
  decide
theorem c4420 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (13 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4418 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4419 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4421 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (13 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4422 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (13 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4420 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4421 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4423 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (13 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4417 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4422 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4424 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (13 : Int) + d4 pattern := by
  omega
theorem c4425 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (13 : Int) + d5 pattern := by
  change (4 : Int) ≤ (13 : Int) + 5
  decide
theorem c4426 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (13 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4424 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4425 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4427 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (13 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4428 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (13 : Int) + d193 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4426 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4427 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4429 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (13 : Int) + d10 pattern := by
  omega
theorem c4430 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (13 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4428 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4431 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (13 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4423 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4430 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4432 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (13 : Int) + d6 pattern := by
  omega
theorem c4433 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (13 : Int) + d7 pattern := by
  change (6 : Int) ≤ (13 : Int) + 7
  decide
theorem c4434 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (13 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4432 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4433 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4435 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (13 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4436 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (13 : Int) + d194 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4434 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4435 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4437 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (13 : Int) + d198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4436 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4438 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (13 : Int) + d203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4437 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4439 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (13 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4431 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4438 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4440 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (13 : Int) + d310 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4441 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (13 : Int) + d314 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4420 pattern childGuard
    simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4440 pattern childGuard
    simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4442 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (13 : Int) + d311 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4443 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (13 : Int) + d315 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4426 pattern childGuard
    simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4442 pattern childGuard
    simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4444 (pattern : Ten) (guard : d350 pattern = 1) : d44 pattern ≤ (13 : Int) + d320 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4441 pattern childGuard
    simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4443 pattern childGuard
    simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4445 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (13 : Int) + d312 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4446 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (13 : Int) + d316 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4434 pattern childGuard
    simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4445 pattern childGuard
    simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4447 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (13 : Int) + d319 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4446 pattern childGuard
    simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4448 (pattern : Ten) (guard : d350 pattern = 1) : d50 pattern ≤ (13 : Int) + d323 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4444 pattern childGuard
    simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4447 pattern childGuard
    simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4449 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (13 : Int) + d8 pattern := by
  omega
theorem c4450 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (13 : Int) + d9 pattern := by
  change (8 : Int) ≤ (13 : Int) + 9
  decide
theorem c4451 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (13 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4449 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4450 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4452 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (13 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4453 (pattern : Ten) (guard : d350 pattern = 1) : d8 pattern ≤ (13 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4451 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4452 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4454 (pattern : Ten) (guard : d350 pattern = 1) : d45 pattern ≤ (13 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4453 pattern childGuard
    simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4455 (pattern : Ten) (guard : d350 pattern = 1) : d51 pattern ≤ (13 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4454 pattern childGuard
    simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4456 (pattern : Ten) (guard : d350 pattern = 1) : d55 pattern ≤ (13 : Int) + d325 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4448 pattern childGuard
    simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4455 pattern childGuard
    simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4457 (pattern : Ten) (guard : d350 pattern = 1) : d160 pattern ≤ (13 : Int) + d344 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4439 pattern childGuard
    simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4456 pattern childGuard
    simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4458 (pattern : Ten) (guard : d350 pattern = 1) : d157 pattern ≤ (13 : Int) + d341 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4443 pattern childGuard
    simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4446 pattern childGuard
    simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4459 (pattern : Ten) (guard : d350 pattern = 1) : d158 pattern ≤ (13 : Int) + d342 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4458 pattern childGuard
    simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4454 pattern childGuard
    simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4460 (pattern : Ten) (guard : d350 pattern = 1) : d159 pattern ≤ (13 : Int) + d343 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4459 pattern childGuard
    simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4461 (pattern : Ten) (guard : d350 pattern = 1) : d161 pattern ≤ (13 : Int) + d345 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4439 pattern childGuard
    simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4460 pattern childGuard
    simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4462 (pattern : Ten) (guard : d350 pattern = 1) : d165 pattern ≤ (13 : Int) + d346 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4457 pattern childGuard
    simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4461 pattern childGuard
    simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4463 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (13 : Int) + d309 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4464 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (13 : Int) + d313 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4415 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4463 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4465 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (13 : Int) + d317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4464 pattern childGuard
    simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4441 pattern childGuard
    simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4466 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (13 : Int) + d318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4443 pattern childGuard
    simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4467 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (13 : Int) + d321 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4465 pattern childGuard
    simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4466 pattern childGuard
    simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4468 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (13 : Int) + d322 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4447 pattern childGuard
    simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4469 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (13 : Int) + d324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4467 pattern childGuard
    simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4468 pattern childGuard
    simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4470 (pattern : Ten) (guard : d350 pattern = 1) : d162 pattern ≤ (13 : Int) + d333 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4469 pattern childGuard
    simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4471 (pattern : Ten) (guard : d350 pattern = 1) : d163 pattern ≤ (13 : Int) + d334 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4456 pattern childGuard
    simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4472 (pattern : Ten) (guard : d350 pattern = 1) : d166 pattern ≤ (13 : Int) + d336 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4470 pattern childGuard
    simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4471 pattern childGuard
    simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4473 (pattern : Ten) (guard : d350 pattern = 1) : d168 pattern ≤ (13 : Int) + d347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4462 pattern childGuard
    simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4472 pattern childGuard
    simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4474 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (13 : Int) + d8 pattern := by
  change (7 : Int) ≤ (13 : Int) + 8
  decide
theorem c4475 (pattern : Ten) (guard : d1 pattern = 1) : d38 pattern ≤ (13 : Int) + d8 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4474 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4449 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4476 (pattern : Ten) (guard : d1 pattern = 1) : d40 pattern ≤ (13 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4475 pattern childGuard
    simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4450 pattern childGuard
    simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4477 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (13 : Int) + d195 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4478 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (13 : Int) + d195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4476 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4477 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4479 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (13 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4478 pattern childGuard
    simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
