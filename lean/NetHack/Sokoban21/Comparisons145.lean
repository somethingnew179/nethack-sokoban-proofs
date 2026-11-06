/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons144
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c20300 (pattern : Twelve) (guard : d1 pattern = 1) : d33 pattern ≤ (2 : Int) + d44 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d33, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20299 pattern childGuard
    simpa only [d33, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20301 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (2 : Int) + d63 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d54, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20300 pattern childGuard
    simpa only [d54, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20302 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (2 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14048 pattern childGuard
    simpa only [d29, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d29, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20303 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (2 : Int) + d64 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13328 pattern childGuard
    simpa only [d55, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20302 pattern childGuard
    simpa only [d55, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20304 (pattern : Twelve) (guard : d1 pattern = 1) : d75 pattern ≤ (2 : Int) + d84 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20301 pattern childGuard
    simpa only [d75, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20303 pattern childGuard
    simpa only [d75, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20305 (pattern : Twelve) (guard : d1 pattern = 1) : d92 pattern ≤ (2 : Int) + d98 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20298 pattern childGuard
    simpa only [d92, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20304 pattern childGuard
    simpa only [d92, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20306 (pattern : Twelve) (guard : d1 pattern = 1) : d102 pattern ≤ (2 : Int) + d106 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20294 pattern childGuard
    simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20305 pattern childGuard
    simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20307 (pattern : Twelve) (guard : d1 pattern = 1) : d76 pattern ≤ (2 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20286 pattern childGuard
    simpa only [d76, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d76, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13290 pattern childGuard
    simpa only [d76, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20308 (pattern : Twelve) (guard : d1 pattern = 1) : d93 pattern ≤ (2 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20285 pattern childGuard
    simpa only [d93, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d93, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20307 pattern childGuard
    simpa only [d93, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20309 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (2 : Int) + d56 pattern := by
  omega
theorem c20310 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (2 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13905 pattern childGuard
    simpa only [d36, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d36, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20311 (pattern : Twelve) (guard : d1 pattern = 1) : d57 pattern ≤ (2 : Int) + d65 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d57, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d57, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20310 pattern childGuard
    simpa only [d57, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20312 (pattern : Twelve) (guard : d1 pattern = 1) : d77 pattern ≤ (2 : Int) + d85 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20309 pattern childGuard
    simpa only [d77, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d77, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20311 pattern childGuard
    simpa only [d77, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20313 (pattern : Twelve) (guard : d1 pattern = 1) : d35 pattern ≤ (2 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d35, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d35, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20314 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (2 : Int) + d66 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d56, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20313 pattern childGuard
    simpa only [d56, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20315 (pattern : Twelve) (guard : d1 pattern = 1) : d78 pattern ≤ (2 : Int) + d86 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20314 pattern childGuard
    simpa only [d78, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d78, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20303 pattern childGuard
    simpa only [d78, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20316 (pattern : Twelve) (guard : d1 pattern = 1) : d94 pattern ≤ (2 : Int) + d99 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20312 pattern childGuard
    simpa only [d94, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d94, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20315 pattern childGuard
    simpa only [d94, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20317 (pattern : Twelve) (guard : d1 pattern = 1) : d103 pattern ≤ (2 : Int) + d107 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20308 pattern childGuard
    simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20316 pattern childGuard
    simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20318 (pattern : Twelve) (guard : d1 pattern = 1) : d110 pattern ≤ (2 : Int) + d112 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20306 pattern childGuard
    simpa only [d110, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d110, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20317 pattern childGuard
    simpa only [d110, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20319 (pattern : Twelve) (guard : d1 pattern = 1) : d37 pattern ≤ (2 : Int) + d46 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13905 pattern childGuard
    simpa only [d37, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13331 pattern childGuard
    simpa only [d37, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20320 (pattern : Twelve) (guard : d1 pattern = 1) : d58 pattern ≤ (2 : Int) + d67 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d58, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20319 pattern childGuard
    simpa only [d58, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20321 (pattern : Twelve) (guard : d1 pattern = 1) : d79 pattern ≤ (2 : Int) + d87 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d79, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20320 pattern childGuard
    simpa only [d79, d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20322 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (2 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d30, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d30, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20323 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (2 : Int) + d68 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20324 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (2 : Int) + d88 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20323 pattern childGuard
    simpa only [d80, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20303 pattern childGuard
    simpa only [d80, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20325 (pattern : Twelve) (guard : d1 pattern = 1) : d95 pattern ≤ (2 : Int) + d100 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20321 pattern childGuard
    simpa only [d95, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20324 pattern childGuard
    simpa only [d95, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20326 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (2 : Int) + d59 pattern := by
  omega
theorem c20327 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (2 : Int) + d38 pattern := by
  omega
theorem c20328 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (2 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13479 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13331 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20329 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (2 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13479 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20328 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20330 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (2 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20329 pattern childGuard
    simpa only [d40, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d40, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20331 (pattern : Twelve) (guard : d1 pattern = 1) : d60 pattern ≤ (2 : Int) + d69 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20327 pattern childGuard
    simpa only [d60, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d60, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20330 pattern childGuard
    simpa only [d60, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20332 (pattern : Twelve) (guard : d1 pattern = 1) : d81 pattern ≤ (2 : Int) + d89 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20326 pattern childGuard
    simpa only [d81, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d81, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20331 pattern childGuard
    simpa only [d81, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20333 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (2 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d39, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d39, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20334 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (2 : Int) + d70 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20327 pattern childGuard
    simpa only [d59, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20333 pattern childGuard
    simpa only [d59, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20335 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (2 : Int) + d41 pattern := by
  omega
theorem c20336 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (2 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14227 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20337 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (2 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13488 pattern childGuard
    simpa only [d12, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14229 pattern childGuard
    simpa only [d12, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20338 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (2 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20336 pattern childGuard
    simpa only [d25, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20337 pattern childGuard
    simpa only [d25, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20339 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (2 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20338 pattern childGuard
    simpa only [d42, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d42, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20340 (pattern : Twelve) (guard : d1 pattern = 1) : d61 pattern ≤ (2 : Int) + d71 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20335 pattern childGuard
    simpa only [d61, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d61, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20339 pattern childGuard
    simpa only [d61, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20341 (pattern : Twelve) (guard : d1 pattern = 1) : d82 pattern ≤ (2 : Int) + d90 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20334 pattern childGuard
    simpa only [d82, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d82, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20340 pattern childGuard
    simpa only [d82, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20342 (pattern : Twelve) (guard : d1 pattern = 1) : d96 pattern ≤ (2 : Int) + d101 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20332 pattern childGuard
    simpa only [d96, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d96, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20341 pattern childGuard
    simpa only [d96, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20343 (pattern : Twelve) (guard : d1 pattern = 1) : d104 pattern ≤ (2 : Int) + d108 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20325 pattern childGuard
    simpa only [d104, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d104, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20342 pattern childGuard
    simpa only [d104, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20344 (pattern : Twelve) (guard : d1 pattern = 1) : d105 pattern ≤ (2 : Int) + d109 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20316 pattern childGuard
    simpa only [d105, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d105, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d105, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20345 (pattern : Twelve) (guard : d1 pattern = 1) : d111 pattern ≤ (2 : Int) + d113 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20343 pattern childGuard
    simpa only [d111, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d111, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20344 pattern childGuard
    simpa only [d111, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20346 (pattern : Twelve) (guard : d1 pattern = 1) : d114 pattern ≤ (2 : Int) + d115 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20318 pattern childGuard
    simpa only [d114, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d114, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20345 pattern childGuard
    simpa only [d114, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20347 (pattern : Twelve) (guard : d0 pattern = 1) : d115 pattern ≤ (2 : Int) + d115 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20348 (pattern : Twelve) (guard : d1871 pattern = 1) : d116 pattern ≤ (2 : Int) + d115 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20346 pattern childGuard
    simpa only [d1871, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20347 pattern childGuard
    simpa only [d1871, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20349 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (2 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d26, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d26, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20350 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (2 : Int) + d779 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13939 pattern childGuard
    simpa only [d27, d779, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d27, d779, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20351 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (2 : Int) + d782 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20349 pattern childGuard
    simpa only [d50, d782, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20350 pattern childGuard
    simpa only [d50, d782, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20352 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (2 : Int) + d788 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d72, d788, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20351 pattern childGuard
    simpa only [d72, d788, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20353 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14572 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20354 (pattern : Twelve) (guard : d1 pattern = 1) : d120 pattern ≤ (2 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d120, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13939 pattern childGuard
    simpa only [d120, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d120, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20338 pattern childGuard
    simpa only [d120, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20355 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (2 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13995 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20356 (pattern : Twelve) (guard : d1 pattern = 1) : d129 pattern ≤ (2 : Int) + d61 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d129, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20354 pattern childGuard
    simpa only [d129, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d129, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20355 pattern childGuard
    simpa only [d129, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20357 (pattern : Twelve) (guard : d1 pattern = 1) : d136 pattern ≤ (2 : Int) + d789 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d136, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20353 pattern childGuard
    simpa only [d136, d789, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d136, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20356 pattern childGuard
    simpa only [d136, d789, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20358 (pattern : Twelve) (guard : d1 pattern = 1) : d144 pattern ≤ (2 : Int) + d794 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d144, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20352 pattern childGuard
    simpa only [d144, d794, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d144, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20357 pattern childGuard
    simpa only [d144, d794, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20359 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (2 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13491 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13575 pattern childGuard
    simpa only [d12, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20360 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (2 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20359 pattern childGuard
    simpa only [d20, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13607 pattern childGuard
    simpa only [d20, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20361 (pattern : Twelve) (guard : d1 pattern = 1) : d31 pattern ≤ (2 : Int) + d44 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d31, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20360 pattern childGuard
    simpa only [d31, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20362 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (2 : Int) + d783 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d52, d783, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20361 pattern childGuard
    simpa only [d52, d783, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20363 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (2 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13488 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20364 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (2 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20363 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20365 (pattern : Twelve) (guard : d1 pattern = 1) : d121 pattern ≤ (2 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d121, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d121, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d121, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20364 pattern childGuard
    simpa only [d121, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20366 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (2 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14510 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13915 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20367 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (2 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14510 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20366 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20368 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (2 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20367 pattern childGuard
    simpa only [d36, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d36, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20369 (pattern : Twelve) (guard : d1 pattern = 1) : d130 pattern ≤ (2 : Int) + d69 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d130, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20365 pattern childGuard
    simpa only [d130, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d130, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20368 pattern childGuard
    simpa only [d130, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20370 (pattern : Twelve) (guard : d1 pattern = 1) : d137 pattern ≤ (2 : Int) + d790 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d137, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20362 pattern childGuard
    simpa only [d137, d790, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d137, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20369 pattern childGuard
    simpa only [d137, d790, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20371 (pattern : Twelve) (guard : d1 pattern = 1) : d35 pattern ≤ (2 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14572 pattern childGuard
    simpa only [d35, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d35, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20372 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (2 : Int) + d70 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d56, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20371 pattern childGuard
    simpa only [d56, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20373 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14572 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20374 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d4 pattern := by
  change (1 : Int) ≤ (2 : Int) + 4
  decide
theorem c20375 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (2 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20374 pattern childGuard
    simpa only [d11, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13491 pattern childGuard
    simpa only [d11, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20376 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (2 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20373 pattern childGuard
    simpa only [d19, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20375 pattern childGuard
    simpa only [d19, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20377 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (2 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20376 pattern childGuard
    simpa only [d29, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d29, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20378 (pattern : Twelve) (guard : d1 pattern = 1) : d129 pattern ≤ (2 : Int) + d71 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d129, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20354 pattern childGuard
    simpa only [d129, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d129, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20377 pattern childGuard
    simpa only [d129, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20379 (pattern : Twelve) (guard : d1 pattern = 1) : d138 pattern ≤ (2 : Int) + d90 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d138, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20372 pattern childGuard
    simpa only [d138, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d138, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20378 pattern childGuard
    simpa only [d138, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20380 (pattern : Twelve) (guard : d1 pattern = 1) : d145 pattern ≤ (2 : Int) + d795 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d145, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20370 pattern childGuard
    simpa only [d145, d795, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d145, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20379 pattern childGuard
    simpa only [d145, d795, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20381 (pattern : Twelve) (guard : d1 pattern = 1) : d149 pattern ≤ (2 : Int) + d798 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d149, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20358 pattern childGuard
    simpa only [d149, d798, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d149, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20380 pattern childGuard
    simpa only [d149, d798, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20382 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (2 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d56, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20313 pattern childGuard
    simpa only [d56, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20383 (pattern : Twelve) (guard : d1 pattern = 1) : d139 pattern ≤ (2 : Int) + d89 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d139, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20382 pattern childGuard
    simpa only [d139, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d139, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20369 pattern childGuard
    simpa only [d139, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20384 (pattern : Twelve) (guard : d1 pattern = 1) : d146 pattern ≤ (2 : Int) + d101 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d146, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20383 pattern childGuard
    simpa only [d146, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d146, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20379 pattern childGuard
    simpa only [d146, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20385 (pattern : Twelve) (guard : d1 pattern = 1) : d150 pattern ≤ (2 : Int) + d799 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d150, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20358 pattern childGuard
    simpa only [d150, d799, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d150, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20384 pattern childGuard
    simpa only [d150, d799, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20386 (pattern : Twelve) (guard : d1 pattern = 1) : d153 pattern ≤ (2 : Int) + d802 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d153, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20381 pattern childGuard
    simpa only [d153, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d153, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20385 pattern childGuard
    simpa only [d153, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20387 (pattern : Twelve) (guard : d1 pattern = 1) : d122 pattern ≤ (2 : Int) + d780 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d122, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20367 pattern childGuard
    simpa only [d122, d780, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d122, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13514 pattern childGuard
    simpa only [d122, d780, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20388 (pattern : Twelve) (guard : d1 pattern = 1) : d131 pattern ≤ (2 : Int) + d784 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d131, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20365 pattern childGuard
    simpa only [d131, d784, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d131, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20387 pattern childGuard
    simpa only [d131, d784, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20389 (pattern : Twelve) (guard : d1 pattern = 1) : d140 pattern ≤ (2 : Int) + d791 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d140, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d140, d791, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d140, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20388 pattern childGuard
    simpa only [d140, d791, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20390 (pattern : Twelve) (guard : d1 pattern = 1) : d123 pattern ≤ (2 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d123, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14572 pattern childGuard
    simpa only [d123, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d123, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13489 pattern childGuard
    simpa only [d123, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20391 (pattern : Twelve) (guard : d1 pattern = 1) : d132 pattern ≤ (2 : Int) + d70 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20322 pattern childGuard
    simpa only [d132, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20390 pattern childGuard
    simpa only [d132, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20392 (pattern : Twelve) (guard : d1 pattern = 1) : d141 pattern ≤ (2 : Int) + d90 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d141, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20391 pattern childGuard
    simpa only [d141, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d141, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20378 pattern childGuard
    simpa only [d141, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20393 (pattern : Twelve) (guard : d1 pattern = 1) : d147 pattern ≤ (2 : Int) + d796 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d147, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20389 pattern childGuard
    simpa only [d147, d796, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d147, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20392 pattern childGuard
    simpa only [d147, d796, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20394 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (2 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d38, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13515 pattern childGuard
    simpa only [d38, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20395 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (2 : Int) + d48 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20394 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20333 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20396 (pattern : Twelve) (guard : d1 pattern = 1) : d118 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13575 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13613 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20397 (pattern : Twelve) (guard : d1 pattern = 1) : d124 pattern ≤ (2 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d124, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d124, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d124, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20396 pattern childGuard
    simpa only [d124, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20398 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (2 : Int) + d5 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13491 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13514 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20399 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (2 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13491 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20398 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20400 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (2 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20399 pattern childGuard
    simpa only [d125, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d125, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20401 (pattern : Twelve) (guard : d1 pattern = 1) : d133 pattern ≤ (2 : Int) + d785 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d133, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20397 pattern childGuard
    simpa only [d133, d785, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d133, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20400 pattern childGuard
    simpa only [d133, d785, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20402 (pattern : Twelve) (guard : d1 pattern = 1) : d142 pattern ≤ (2 : Int) + d792 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d142, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20395 pattern childGuard
    simpa only [d142, d792, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d142, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20401 pattern childGuard
    simpa only [d142, d792, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20403 (pattern : Twelve) (guard : d1 pattern = 1) : d126 pattern ≤ (2 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d126, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13575 pattern childGuard
    simpa only [d126, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20404 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13489 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20405 (pattern : Twelve) (guard : d1 pattern = 1) : d134 pattern ≤ (2 : Int) + d786 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20403 pattern childGuard
    simpa only [d134, d786, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20404 pattern childGuard
    simpa only [d134, d786, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20406 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (2 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d9, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13491 pattern childGuard
    simpa only [d9, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20407 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (2 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13482 pattern childGuard
    simpa only [d23, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20406 pattern childGuard
    simpa only [d23, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20408 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13613 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20409 (pattern : Twelve) (guard : d1 pattern = 1) : d127 pattern ≤ (2 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20407 pattern childGuard
    simpa only [d127, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20408 pattern childGuard
    simpa only [d127, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20410 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13608 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20411 (pattern : Twelve) (guard : d1 pattern = 1) : d135 pattern ≤ (2 : Int) + d787 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d135, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20409 pattern childGuard
    simpa only [d135, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d135, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20410 pattern childGuard
    simpa only [d135, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20412 (pattern : Twelve) (guard : d1 pattern = 1) : d143 pattern ≤ (2 : Int) + d793 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d143, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20405 pattern childGuard
    simpa only [d143, d793, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d143, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20411 pattern childGuard
    simpa only [d143, d793, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20413 (pattern : Twelve) (guard : d1 pattern = 1) : d148 pattern ≤ (2 : Int) + d797 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d148, d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20402 pattern childGuard
    simpa only [d148, d797, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d148, d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20412 pattern childGuard
    simpa only [d148, d797, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20414 (pattern : Twelve) (guard : d1 pattern = 1) : d151 pattern ≤ (2 : Int) + d800 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d151, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20393 pattern childGuard
    simpa only [d151, d800, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d151, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20413 pattern childGuard
    simpa only [d151, d800, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20415 (pattern : Twelve) (guard : d1 pattern = 1) : d152 pattern ≤ (2 : Int) + d801 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d152, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20384 pattern childGuard
    simpa only [d152, d801, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d152, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d152, d801, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20416 (pattern : Twelve) (guard : d1 pattern = 1) : d154 pattern ≤ (2 : Int) + d803 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d154, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20414 pattern childGuard
    simpa only [d154, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d154, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20415 pattern childGuard
    simpa only [d154, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20417 (pattern : Twelve) (guard : d1 pattern = 1) : d155 pattern ≤ (2 : Int) + d804 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d155, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20386 pattern childGuard
    simpa only [d155, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d155, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20416 pattern childGuard
    simpa only [d155, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20418 (pattern : Twelve) (guard : d0 pattern = 1) : d804 pattern ≤ (2 : Int) + d804 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20419 (pattern : Twelve) (guard : d1871 pattern = 1) : d805 pattern ≤ (2 : Int) + d804 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1871, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20417 pattern childGuard
    simpa only [d1871, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1871, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20418 pattern childGuard
    simpa only [d1871, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20420 (pattern : Twelve) (guard : d1871 pattern = 1) : d806 pattern ≤ (2 : Int) + d3237 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1871 pattern = 1 := by simpa only [d806, d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20348 pattern childGuard
    simpa only [d806, d3237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1871 pattern = 1 := by simpa only [d806, d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20419 pattern childGuard
    simpa only [d806, d3237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20421 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (2 : Int) + d838 pattern := by
  omega
theorem c20422 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (2 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14010 pattern childGuard
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20423 (pattern : Twelve) (guard : d1 pattern = 1) : d839 pattern ≤ (2 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20422 pattern childGuard
    simpa only [d839, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13361 pattern childGuard
    simpa only [d839, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20424 (pattern : Twelve) (guard : d1 pattern = 1) : d853 pattern ≤ (2 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20421 pattern childGuard
    simpa only [d853, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20423 pattern childGuard
    simpa only [d853, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20425 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (2 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13984 pattern childGuard
    simpa only [d818, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d818, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20426 (pattern : Twelve) (guard : d1 pattern = 1) : d826 pattern ≤ (2 : Int) + d832 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13328 pattern childGuard
    simpa only [d826, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20425 pattern childGuard
    simpa only [d826, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20427 (pattern : Twelve) (guard : d1 pattern = 1) : d840 pattern ≤ (2 : Int) + d847 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20309 pattern childGuard
    simpa only [d840, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20426 pattern childGuard
    simpa only [d840, d847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20428 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (2 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14010 pattern childGuard
    simpa only [d36, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d36, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20429 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (2 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13328 pattern childGuard
    simpa only [d827, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20428 pattern childGuard
    simpa only [d827, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20430 (pattern : Twelve) (guard : d1 pattern = 1) : d841 pattern ≤ (2 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20429 pattern childGuard
    simpa only [d841, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13361 pattern childGuard
    simpa only [d841, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20431 (pattern : Twelve) (guard : d1 pattern = 1) : d854 pattern ≤ (2 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20427 pattern childGuard
    simpa only [d854, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20430 pattern childGuard
    simpa only [d854, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20432 (pattern : Twelve) (guard : d1 pattern = 1) : d861 pattern ≤ (2 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20424 pattern childGuard
    simpa only [d861, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20431 pattern childGuard
    simpa only [d861, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20433 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (2 : Int) + d46 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13984 pattern childGuard
    simpa only [d819, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13331 pattern childGuard
    simpa only [d819, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20434 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (2 : Int) + d834 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13328 pattern childGuard
    simpa only [d828, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20433 pattern childGuard
    simpa only [d828, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20435 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (2 : Int) + d849 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d842, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20434 pattern childGuard
    simpa only [d842, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20436 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (2 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14010 pattern childGuard
    simpa only [d34, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20364 pattern childGuard
    simpa only [d34, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20437 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (2 : Int) + d835 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13328 pattern childGuard
    simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20436 pattern childGuard
    simpa only [d835, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20438 (pattern : Twelve) (guard : d1 pattern = 1) : d843 pattern ≤ (2 : Int) + d850 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20437 pattern childGuard
    simpa only [d843, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13361 pattern childGuard
    simpa only [d843, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20439 (pattern : Twelve) (guard : d1 pattern = 1) : d855 pattern ≤ (2 : Int) + d859 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20435 pattern childGuard
    simpa only [d855, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20438 pattern childGuard
    simpa only [d855, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
