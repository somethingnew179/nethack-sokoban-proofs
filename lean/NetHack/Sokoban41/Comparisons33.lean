/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons32
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c5280 (pattern : Ten) (guard : d748 pattern = 1) : d54 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d747 pattern = 1 := by simpa only [d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5278 pattern childGuard
    simpa only [d748, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5279 pattern childGuard
    simpa only [d748, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5281 (pattern : Ten) (guard : d749 pattern = 1) : d54 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d748 pattern = 1 := by simpa only [d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5280 pattern childGuard
    simpa only [d749, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5279 pattern childGuard
    simpa only [d749, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5282 (pattern : Ten) (guard : d0 pattern = 1) : d62 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5283 (pattern : Ten) (guard : d750 pattern = 1) : d64 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d749 pattern = 1 := by simpa only [d750, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5281 pattern childGuard
    simpa only [d750, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d750, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5282 pattern childGuard
    simpa only [d750, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5284 (pattern : Ten) (guard : d0 pattern = 1) : d65 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5285 (pattern : Ten) (guard : d751 pattern = 1) : d66 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d750 pattern = 1 := by simpa only [d751, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5283 pattern childGuard
    simpa only [d751, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d751, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d751, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5286 (pattern : Ten) (guard : d0 pattern = 1) : d71 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5287 (pattern : Ten) (guard : d748 pattern = 1) : d73 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d747 pattern = 1 := by simpa only [d748, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5264 pattern childGuard
    simpa only [d748, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d748, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5286 pattern childGuard
    simpa only [d748, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5288 (pattern : Ten) (guard : d0 pattern = 1) : d74 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5289 (pattern : Ten) (guard : d749 pattern = 1) : d77 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d748 pattern = 1 := by simpa only [d749, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5287 pattern childGuard
    simpa only [d749, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d749, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5288 pattern childGuard
    simpa only [d749, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5290 (pattern : Ten) (guard : d0 pattern = 1) : d78 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5291 (pattern : Ten) (guard : d750 pattern = 1) : d79 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d749 pattern = 1 := by simpa only [d750, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5289 pattern childGuard
    simpa only [d750, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d750, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5290 pattern childGuard
    simpa only [d750, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5292 (pattern : Ten) (guard : d0 pattern = 1) : d80 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5293 (pattern : Ten) (guard : d751 pattern = 1) : d81 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d750 pattern = 1 := by simpa only [d751, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5291 pattern childGuard
    simpa only [d751, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d751, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5292 pattern childGuard
    simpa only [d751, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5294 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5295 (pattern : Ten) (guard : d749 pattern = 1) : d82 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d748 pattern = 1 := by simpa only [d749, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5280 pattern childGuard
    simpa only [d749, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d749, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5294 pattern childGuard
    simpa only [d749, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5296 (pattern : Ten) (guard : d0 pattern = 1) : d58 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5297 (pattern : Ten) (guard : d750 pattern = 1) : d83 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d749 pattern = 1 := by simpa only [d750, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5295 pattern childGuard
    simpa only [d750, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d750, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5296 pattern childGuard
    simpa only [d750, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5298 (pattern : Ten) (guard : d0 pattern = 1) : d84 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5299 (pattern : Ten) (guard : d751 pattern = 1) : d85 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d750 pattern = 1 := by simpa only [d751, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5297 pattern childGuard
    simpa only [d751, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d751, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5298 pattern childGuard
    simpa only [d751, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5300 (pattern : Ten) (guard : d0 pattern = 1) : d86 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5301 (pattern : Ten) (guard : d606 pattern = 1) : d0 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem c5302 (pattern : Ten) (guard : d746 pattern = 1) : d87 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d746, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5300 pattern childGuard
    simpa only [d746, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d606 pattern = 1 := by simpa only [d746, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5301 pattern childGuard
    simpa only [d746, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5303 (pattern : Ten) (guard : d0 pattern = 1) : d88 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5304 (pattern : Ten) (guard : d747 pattern = 1) : d93 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d746 pattern = 1 := by simpa only [d747, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5302 pattern childGuard
    simpa only [d747, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d747, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5303 pattern childGuard
    simpa only [d747, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5305 (pattern : Ten) (guard : d0 pattern = 1) : d94 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5306 (pattern : Ten) (guard : d748 pattern = 1) : d99 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d747 pattern = 1 := by simpa only [d748, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5304 pattern childGuard
    simpa only [d748, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d748, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5305 pattern childGuard
    simpa only [d748, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5307 (pattern : Ten) (guard : d0 pattern = 1) : d100 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5308 (pattern : Ten) (guard : d749 pattern = 1) : d103 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d748 pattern = 1 := by simpa only [d749, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5306 pattern childGuard
    simpa only [d749, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d749, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5307 pattern childGuard
    simpa only [d749, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5309 (pattern : Ten) (guard : d0 pattern = 1) : d104 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5310 (pattern : Ten) (guard : d750 pattern = 1) : d105 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d749 pattern = 1 := by simpa only [d750, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5308 pattern childGuard
    simpa only [d750, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d750, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5309 pattern childGuard
    simpa only [d750, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5311 (pattern : Ten) (guard : d0 pattern = 1) : d106 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5312 (pattern : Ten) (guard : d751 pattern = 1) : d107 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d750 pattern = 1 := by simpa only [d751, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5310 pattern childGuard
    simpa only [d751, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d751, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5311 pattern childGuard
    simpa only [d751, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5313 (pattern : Ten) (guard : d606 pattern = 1) : d5 pattern ≤ (0 : Int) + d5 pattern := by
  omega
theorem c5314 (pattern : Ten) (guard : d746 pattern = 1) : d108 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d746, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5273 pattern childGuard
    simpa only [d746, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d606 pattern = 1 := by simpa only [d746, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5313 pattern childGuard
    simpa only [d746, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5315 (pattern : Ten) (guard : d747 pattern = 1) : d109 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d746 pattern = 1 := by simpa only [d747, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5314 pattern childGuard
    simpa only [d747, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d747, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5273 pattern childGuard
    simpa only [d747, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5316 (pattern : Ten) (guard : d0 pattern = 1) : d110 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5317 (pattern : Ten) (guard : d748 pattern = 1) : d115 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d747 pattern = 1 := by simpa only [d748, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5315 pattern childGuard
    simpa only [d748, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d748, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5316 pattern childGuard
    simpa only [d748, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5318 (pattern : Ten) (guard : d0 pattern = 1) : d116 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5319 (pattern : Ten) (guard : d749 pattern = 1) : d119 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d748 pattern = 1 := by simpa only [d749, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5317 pattern childGuard
    simpa only [d749, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d749, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5318 pattern childGuard
    simpa only [d749, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5320 (pattern : Ten) (guard : d0 pattern = 1) : d120 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5321 (pattern : Ten) (guard : d750 pattern = 1) : d121 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d749 pattern = 1 := by simpa only [d750, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5319 pattern childGuard
    simpa only [d750, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d750, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5320 pattern childGuard
    simpa only [d750, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5322 (pattern : Ten) (guard : d0 pattern = 1) : d122 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5323 (pattern : Ten) (guard : d751 pattern = 1) : d123 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d750 pattern = 1 := by simpa only [d751, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5321 pattern childGuard
    simpa only [d751, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d751, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5322 pattern childGuard
    simpa only [d751, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5324 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5325 (pattern : Ten) (guard : d747 pattern = 1) : d124 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d746 pattern = 1 := by simpa only [d747, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5276 pattern childGuard
    simpa only [d747, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d747, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5324 pattern childGuard
    simpa only [d747, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5326 (pattern : Ten) (guard : d0 pattern = 1) : d48 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5327 (pattern : Ten) (guard : d748 pattern = 1) : d125 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d747 pattern = 1 := by simpa only [d748, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5325 pattern childGuard
    simpa only [d748, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d748, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5326 pattern childGuard
    simpa only [d748, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5328 (pattern : Ten) (guard : d749 pattern = 1) : d128 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d748 pattern = 1 := by simpa only [d749, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5327 pattern childGuard
    simpa only [d749, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d749, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5326 pattern childGuard
    simpa only [d749, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5329 (pattern : Ten) (guard : d0 pattern = 1) : d129 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5330 (pattern : Ten) (guard : d750 pattern = 1) : d130 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d749 pattern = 1 := by simpa only [d750, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d750, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d750, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5329 pattern childGuard
    simpa only [d750, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5331 (pattern : Ten) (guard : d0 pattern = 1) : d131 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5332 (pattern : Ten) (guard : d751 pattern = 1) : d132 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d750 pattern = 1 := by simpa only [d751, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5330 pattern childGuard
    simpa only [d751, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d751, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5331 pattern childGuard
    simpa only [d751, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5333 (pattern : Ten) (guard : d751 pattern = 1) : d133 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d750 pattern = 1 := by simpa only [d751, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5283 pattern childGuard
    simpa only [d751, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d751, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5294 pattern childGuard
    simpa only [d751, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5334 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5335 (pattern : Ten) (guard : d750 pattern = 1) : d134 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d749 pattern = 1 := by simpa only [d750, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5281 pattern childGuard
    simpa only [d750, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d750, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5334 pattern childGuard
    simpa only [d750, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5336 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5337 (pattern : Ten) (guard : d751 pattern = 1) : d135 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d750 pattern = 1 := by simpa only [d751, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5335 pattern childGuard
    simpa only [d751, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d751, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5336 pattern childGuard
    simpa only [d751, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5338 (pattern : Ten) (guard : d0 pattern = 1) : d138 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5339 (pattern : Ten) (guard : d746 pattern = 1) : d139 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d746, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5338 pattern childGuard
    simpa only [d746, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d606 pattern = 1 := by simpa only [d746, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5261 pattern childGuard
    simpa only [d746, d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5340 (pattern : Ten) (guard : d747 pattern = 1) : d142 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d746 pattern = 1 := by simpa only [d747, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5339 pattern childGuard
    simpa only [d747, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d747, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5263 pattern childGuard
    simpa only [d747, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5341 (pattern : Ten) (guard : d0 pattern = 1) : d143 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5342 (pattern : Ten) (guard : d748 pattern = 1) : d145 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d747 pattern = 1 := by simpa only [d748, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5340 pattern childGuard
    simpa only [d748, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d748, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5341 pattern childGuard
    simpa only [d748, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5343 (pattern : Ten) (guard : d0 pattern = 1) : d146 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5344 (pattern : Ten) (guard : d749 pattern = 1) : d147 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d748 pattern = 1 := by simpa only [d749, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5342 pattern childGuard
    simpa only [d749, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d749, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5343 pattern childGuard
    simpa only [d749, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5345 (pattern : Ten) (guard : d750 pattern = 1) : d148 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d749 pattern = 1 := by simpa only [d750, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5344 pattern childGuard
    simpa only [d750, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d750, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5269 pattern childGuard
    simpa only [d750, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5346 (pattern : Ten) (guard : d751 pattern = 1) : d149 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d750 pattern = 1 := by simpa only [d751, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5345 pattern childGuard
    simpa only [d751, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d751, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d751, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5347 (pattern : Ten) (guard : d0 pattern = 1) : d9 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5348 (pattern : Ten) (guard : d748 pattern = 1) : d150 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d747 pattern = 1 := by simpa only [d748, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5278 pattern childGuard
    simpa only [d748, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d748, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5347 pattern childGuard
    simpa only [d748, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5349 (pattern : Ten) (guard : d749 pattern = 1) : d151 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d748 pattern = 1 := by simpa only [d749, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5348 pattern childGuard
    simpa only [d749, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d749, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5279 pattern childGuard
    simpa only [d749, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5350 (pattern : Ten) (guard : d0 pattern = 1) : d152 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5351 (pattern : Ten) (guard : d750 pattern = 1) : d154 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d749 pattern = 1 := by simpa only [d750, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5349 pattern childGuard
    simpa only [d750, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d750, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5350 pattern childGuard
    simpa only [d750, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5352 (pattern : Ten) (guard : d0 pattern = 1) : d155 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5353 (pattern : Ten) (guard : d751 pattern = 1) : d156 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d750 pattern = 1 := by simpa only [d751, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5351 pattern childGuard
    simpa only [d751, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d751, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5352 pattern childGuard
    simpa only [d751, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5354 (pattern : Ten) (guard : d0 pattern = 1) : d55 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5355 (pattern : Ten) (guard : d748 pattern = 1) : d160 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d747 pattern = 1 := by simpa only [d748, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5278 pattern childGuard
    simpa only [d748, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d748, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5354 pattern childGuard
    simpa only [d748, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5356 (pattern : Ten) (guard : d0 pattern = 1) : d161 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5357 (pattern : Ten) (guard : d749 pattern = 1) : d165 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d748 pattern = 1 := by simpa only [d749, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5355 pattern childGuard
    simpa only [d749, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d749, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5356 pattern childGuard
    simpa only [d749, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5358 (pattern : Ten) (guard : d0 pattern = 1) : d166 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5359 (pattern : Ten) (guard : d750 pattern = 1) : d168 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d749 pattern = 1 := by simpa only [d750, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5357 pattern childGuard
    simpa only [d750, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d750, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5358 pattern childGuard
    simpa only [d750, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5360 (pattern : Ten) (guard : d0 pattern = 1) : d169 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5361 (pattern : Ten) (guard : d751 pattern = 1) : d170 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d750 pattern = 1 := by simpa only [d751, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5359 pattern childGuard
    simpa only [d751, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d751, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5360 pattern childGuard
    simpa only [d751, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5362 (pattern : Ten) (guard : d752 pattern = 1) : d0 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) ≤ (0 : Int) + 4
  decide
theorem c5363 (pattern : Ten) (guard : d0 pattern = 1) : d12 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5364 (pattern : Ten) (guard : d753 pattern = 1) : d17 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d752 pattern = 1 := by simpa only [d753, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5362 pattern childGuard
    simpa only [d753, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d753, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5363 pattern childGuard
    simpa only [d753, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5365 (pattern : Ten) (guard : d0 pattern = 1) : d18 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5366 (pattern : Ten) (guard : d754 pattern = 1) : d23 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d753 pattern = 1 := by simpa only [d754, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5364 pattern childGuard
    simpa only [d754, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d754, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5365 pattern childGuard
    simpa only [d754, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5367 (pattern : Ten) (guard : d0 pattern = 1) : d24 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5368 (pattern : Ten) (guard : d755 pattern = 1) : d29 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d754 pattern = 1 := by simpa only [d755, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5366 pattern childGuard
    simpa only [d755, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d755, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5367 pattern childGuard
    simpa only [d755, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5369 (pattern : Ten) (guard : d0 pattern = 1) : d30 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5370 (pattern : Ten) (guard : d756 pattern = 1) : d33 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d755 pattern = 1 := by simpa only [d756, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5368 pattern childGuard
    simpa only [d756, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d756, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5369 pattern childGuard
    simpa only [d756, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5371 (pattern : Ten) (guard : d0 pattern = 1) : d34 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5372 (pattern : Ten) (guard : d757 pattern = 1) : d35 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d756 pattern = 1 := by simpa only [d757, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5370 pattern childGuard
    simpa only [d757, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d757, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5371 pattern childGuard
    simpa only [d757, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5373 (pattern : Ten) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5374 (pattern : Ten) (guard : d758 pattern = 1) : d37 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d757 pattern = 1 := by simpa only [d758, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5372 pattern childGuard
    simpa only [d758, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d758, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5373 pattern childGuard
    simpa only [d758, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5375 (pattern : Ten) (guard : d359 pattern = 1) : d2 pattern ≤ (0 : Int) + d4 pattern := by
  change (2 : Int) ≤ (0 : Int) + 4
  decide
theorem c5376 (pattern : Ten) (guard : d752 pattern = 1) : d15 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d752, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c394 pattern childGuard
    simpa only [d752, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d752, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5375 pattern childGuard
    simpa only [d752, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5377 (pattern : Ten) (guard : d0 pattern = 1) : d42 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5378 (pattern : Ten) (guard : d753 pattern = 1) : d48 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d752 pattern = 1 := by simpa only [d753, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5376 pattern childGuard
    simpa only [d753, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d753, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5377 pattern childGuard
    simpa only [d753, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5379 (pattern : Ten) (guard : d0 pattern = 1) : d49 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5380 (pattern : Ten) (guard : d754 pattern = 1) : d54 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d753 pattern = 1 := by simpa only [d754, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5378 pattern childGuard
    simpa only [d754, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d754, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5379 pattern childGuard
    simpa only [d754, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5381 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5382 (pattern : Ten) (guard : d755 pattern = 1) : d54 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d754 pattern = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5380 pattern childGuard
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5381 pattern childGuard
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5383 (pattern : Ten) (guard : d756 pattern = 1) : d54 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d755 pattern = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5382 pattern childGuard
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5381 pattern childGuard
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5384 (pattern : Ten) (guard : d0 pattern = 1) : d62 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5385 (pattern : Ten) (guard : d757 pattern = 1) : d64 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d756 pattern = 1 := by simpa only [d757, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5383 pattern childGuard
    simpa only [d757, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d757, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5384 pattern childGuard
    simpa only [d757, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5386 (pattern : Ten) (guard : d0 pattern = 1) : d65 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5387 (pattern : Ten) (guard : d758 pattern = 1) : d66 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d757 pattern = 1 := by simpa only [d758, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5385 pattern childGuard
    simpa only [d758, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d758, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5386 pattern childGuard
    simpa only [d758, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5388 (pattern : Ten) (guard : d0 pattern = 1) : d71 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5389 (pattern : Ten) (guard : d755 pattern = 1) : d73 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d754 pattern = 1 := by simpa only [d755, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5366 pattern childGuard
    simpa only [d755, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d755, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5388 pattern childGuard
    simpa only [d755, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5390 (pattern : Ten) (guard : d0 pattern = 1) : d74 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5391 (pattern : Ten) (guard : d756 pattern = 1) : d77 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d755 pattern = 1 := by simpa only [d756, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5389 pattern childGuard
    simpa only [d756, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d756, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5390 pattern childGuard
    simpa only [d756, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5392 (pattern : Ten) (guard : d0 pattern = 1) : d78 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5393 (pattern : Ten) (guard : d757 pattern = 1) : d79 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d756 pattern = 1 := by simpa only [d757, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5391 pattern childGuard
    simpa only [d757, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d757, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5392 pattern childGuard
    simpa only [d757, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5394 (pattern : Ten) (guard : d0 pattern = 1) : d80 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5395 (pattern : Ten) (guard : d758 pattern = 1) : d81 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d757 pattern = 1 := by simpa only [d758, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5393 pattern childGuard
    simpa only [d758, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d758, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5394 pattern childGuard
    simpa only [d758, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5396 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5397 (pattern : Ten) (guard : d756 pattern = 1) : d82 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d755 pattern = 1 := by simpa only [d756, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5382 pattern childGuard
    simpa only [d756, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d756, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5396 pattern childGuard
    simpa only [d756, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5398 (pattern : Ten) (guard : d0 pattern = 1) : d58 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5399 (pattern : Ten) (guard : d757 pattern = 1) : d83 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d756 pattern = 1 := by simpa only [d757, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5397 pattern childGuard
    simpa only [d757, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d757, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5398 pattern childGuard
    simpa only [d757, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5400 (pattern : Ten) (guard : d0 pattern = 1) : d84 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5401 (pattern : Ten) (guard : d758 pattern = 1) : d85 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d757 pattern = 1 := by simpa only [d758, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5399 pattern childGuard
    simpa only [d758, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d758, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5400 pattern childGuard
    simpa only [d758, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5402 (pattern : Ten) (guard : d359 pattern = 1) : d4 pattern ≤ (0 : Int) + d4 pattern := by
  omega
theorem c5403 (pattern : Ten) (guard : d752 pattern = 1) : d86 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d752, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c394 pattern childGuard
    simpa only [d752, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d752, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5402 pattern childGuard
    simpa only [d752, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5404 (pattern : Ten) (guard : d753 pattern = 1) : d87 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d752 pattern = 1 := by simpa only [d753, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5403 pattern childGuard
    simpa only [d753, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d753, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c394 pattern childGuard
    simpa only [d753, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5405 (pattern : Ten) (guard : d0 pattern = 1) : d88 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5406 (pattern : Ten) (guard : d754 pattern = 1) : d93 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d753 pattern = 1 := by simpa only [d754, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5404 pattern childGuard
    simpa only [d754, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d754, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5405 pattern childGuard
    simpa only [d754, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5407 (pattern : Ten) (guard : d0 pattern = 1) : d94 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5408 (pattern : Ten) (guard : d755 pattern = 1) : d99 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d754 pattern = 1 := by simpa only [d755, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5406 pattern childGuard
    simpa only [d755, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d755, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5407 pattern childGuard
    simpa only [d755, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5409 (pattern : Ten) (guard : d0 pattern = 1) : d100 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5410 (pattern : Ten) (guard : d756 pattern = 1) : d103 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d755 pattern = 1 := by simpa only [d756, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5408 pattern childGuard
    simpa only [d756, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d756, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5409 pattern childGuard
    simpa only [d756, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5411 (pattern : Ten) (guard : d0 pattern = 1) : d104 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5412 (pattern : Ten) (guard : d757 pattern = 1) : d105 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d756 pattern = 1 := by simpa only [d757, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5410 pattern childGuard
    simpa only [d757, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d757, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5411 pattern childGuard
    simpa only [d757, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5413 (pattern : Ten) (guard : d0 pattern = 1) : d106 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5414 (pattern : Ten) (guard : d758 pattern = 1) : d107 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d757 pattern = 1 := by simpa only [d758, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5412 pattern childGuard
    simpa only [d758, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d758, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5413 pattern childGuard
    simpa only [d758, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5415 (pattern : Ten) (guard : d0 pattern = 1) : d5 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5416 (pattern : Ten) (guard : d753 pattern = 1) : d108 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d752 pattern = 1 := by simpa only [d753, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5376 pattern childGuard
    simpa only [d753, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d753, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5415 pattern childGuard
    simpa only [d753, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5417 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5418 (pattern : Ten) (guard : d754 pattern = 1) : d109 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d753 pattern = 1 := by simpa only [d754, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5416 pattern childGuard
    simpa only [d754, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d754, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5417 pattern childGuard
    simpa only [d754, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5419 (pattern : Ten) (guard : d0 pattern = 1) : d110 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5420 (pattern : Ten) (guard : d755 pattern = 1) : d115 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d754 pattern = 1 := by simpa only [d755, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5418 pattern childGuard
    simpa only [d755, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d755, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5419 pattern childGuard
    simpa only [d755, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5421 (pattern : Ten) (guard : d0 pattern = 1) : d116 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5422 (pattern : Ten) (guard : d756 pattern = 1) : d119 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d755 pattern = 1 := by simpa only [d756, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5420 pattern childGuard
    simpa only [d756, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d756, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5421 pattern childGuard
    simpa only [d756, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5423 (pattern : Ten) (guard : d0 pattern = 1) : d120 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5424 (pattern : Ten) (guard : d757 pattern = 1) : d121 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d756 pattern = 1 := by simpa only [d757, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5422 pattern childGuard
    simpa only [d757, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d757, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5423 pattern childGuard
    simpa only [d757, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5425 (pattern : Ten) (guard : d0 pattern = 1) : d122 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5426 (pattern : Ten) (guard : d758 pattern = 1) : d123 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d757 pattern = 1 := by simpa only [d758, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5424 pattern childGuard
    simpa only [d758, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d758, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5425 pattern childGuard
    simpa only [d758, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5427 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5428 (pattern : Ten) (guard : d754 pattern = 1) : d124 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d753 pattern = 1 := by simpa only [d754, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5378 pattern childGuard
    simpa only [d754, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d754, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5427 pattern childGuard
    simpa only [d754, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5429 (pattern : Ten) (guard : d0 pattern = 1) : d48 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5430 (pattern : Ten) (guard : d755 pattern = 1) : d125 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d754 pattern = 1 := by simpa only [d755, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5428 pattern childGuard
    simpa only [d755, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d755, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5429 pattern childGuard
    simpa only [d755, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5431 (pattern : Ten) (guard : d756 pattern = 1) : d128 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d755 pattern = 1 := by simpa only [d756, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5430 pattern childGuard
    simpa only [d756, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d756, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5429 pattern childGuard
    simpa only [d756, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5432 (pattern : Ten) (guard : d0 pattern = 1) : d129 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5433 (pattern : Ten) (guard : d757 pattern = 1) : d130 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d756 pattern = 1 := by simpa only [d757, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5431 pattern childGuard
    simpa only [d757, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d757, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5432 pattern childGuard
    simpa only [d757, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5434 (pattern : Ten) (guard : d0 pattern = 1) : d131 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5435 (pattern : Ten) (guard : d758 pattern = 1) : d132 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d757 pattern = 1 := by simpa only [d758, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5433 pattern childGuard
    simpa only [d758, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d758, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5434 pattern childGuard
    simpa only [d758, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5436 (pattern : Ten) (guard : d758 pattern = 1) : d133 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d757 pattern = 1 := by simpa only [d758, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5385 pattern childGuard
    simpa only [d758, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d758, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5396 pattern childGuard
    simpa only [d758, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5437 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5438 (pattern : Ten) (guard : d757 pattern = 1) : d134 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d756 pattern = 1 := by simpa only [d757, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5383 pattern childGuard
    simpa only [d757, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d757, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5437 pattern childGuard
    simpa only [d757, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5439 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban41.Diagram
