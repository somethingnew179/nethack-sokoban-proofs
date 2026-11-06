/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons15
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c2560 (pattern : Ten) (guard : d447 pattern = 1) : d22 pattern ≤ (1 : Int) + d179 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2558 pattern childGuard
    simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2493 pattern childGuard
    simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2561 (pattern : Ten) (guard : d447 pattern = 1) : d25 pattern ≤ (1 : Int) + d182 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2559 pattern childGuard
    simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2560 pattern childGuard
    simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2562 (pattern : Ten) (guard : d447 pattern = 1) : d74 pattern ≤ (1 : Int) + d185 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d74, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2561 pattern childGuard
    simpa only [d74, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d74, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2551 pattern childGuard
    simpa only [d74, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2563 (pattern : Ten) (guard : d447 pattern = 1) : d77 pattern ≤ (1 : Int) + d188 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d77, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2552 pattern childGuard
    simpa only [d77, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d77, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2562 pattern childGuard
    simpa only [d77, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2564 (pattern : Ten) (guard : d447 pattern = 1) : d26 pattern ≤ (1 : Int) + d181 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2544 pattern childGuard
    simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2493 pattern childGuard
    simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2565 (pattern : Ten) (guard : d447 pattern = 1) : d72 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2550 pattern childGuard
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2493 pattern childGuard
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2566 (pattern : Ten) (guard : d447 pattern = 1) : d75 pattern ≤ (1 : Int) + d186 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d75, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2564 pattern childGuard
    simpa only [d75, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d75, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2565 pattern childGuard
    simpa only [d75, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2567 (pattern : Ten) (guard : d447 pattern = 1) : d28 pattern ≤ (1 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2560 pattern childGuard
    simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2493 pattern childGuard
    simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2568 (pattern : Ten) (guard : d447 pattern = 1) : d76 pattern ≤ (1 : Int) + d187 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d76, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2567 pattern childGuard
    simpa only [d76, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d76, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2565 pattern childGuard
    simpa only [d76, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2569 (pattern : Ten) (guard : d447 pattern = 1) : d78 pattern ≤ (1 : Int) + d189 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d78, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2566 pattern childGuard
    simpa only [d78, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d78, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2568 pattern childGuard
    simpa only [d78, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2570 (pattern : Ten) (guard : d447 pattern = 1) : d79 pattern ≤ (1 : Int) + d190 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d79, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2563 pattern childGuard
    simpa only [d79, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d79, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2569 pattern childGuard
    simpa only [d79, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2571 (pattern : Ten) (guard : d447 pattern = 1) : d80 pattern ≤ (1 : Int) + d191 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d80, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2569 pattern childGuard
    simpa only [d80, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d80, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2493 pattern childGuard
    simpa only [d80, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2572 (pattern : Ten) (guard : d447 pattern = 1) : d81 pattern ≤ (1 : Int) + d192 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d447 pattern = 1 := by simpa only [d81, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2570 pattern childGuard
    simpa only [d81, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d447 pattern = 1 := by simpa only [d81, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2571 pattern childGuard
    simpa only [d81, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2573 (pattern : Ten) (guard : d360 pattern = 1) : d0 pattern ≤ (1 : Int) + d10 pattern := by
  change (0 : Int) ≤ (1 : Int) + 10
  decide
theorem c2574 (pattern : Ten) (guard : d446 pattern = 1) : d221 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d446, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2573 pattern childGuard
    simpa only [d446, d221, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d446, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1913 pattern childGuard
    simpa only [d446, d221, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2575 (pattern : Ten) (guard : d446 pattern = 1) : d0 pattern ≤ (1 : Int) + d10 pattern := by
  change (0 : Int) ≤ (1 : Int) + 10
  decide
theorem c2576 (pattern : Ten) (guard : d446 pattern = 1) : d222 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2574 pattern childGuard
    simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2575 pattern childGuard
    simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2577 (pattern : Ten) (guard : d446 pattern = 1) : d223 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2576 pattern childGuard
    simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2575 pattern childGuard
    simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2578 (pattern : Ten) (guard : d446 pattern = 1) : d12 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2575 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2579 (pattern : Ten) (guard : d446 pattern = 1) : d224 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2577 pattern childGuard
    simpa only [d224, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2578 pattern childGuard
    simpa only [d224, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2580 (pattern : Ten) (guard : d446 pattern = 1) : d18 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2578 pattern childGuard
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2581 (pattern : Ten) (guard : d446 pattern = 1) : d225 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2579 pattern childGuard
    simpa only [d225, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2580 pattern childGuard
    simpa only [d225, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2582 (pattern : Ten) (guard : d446 pattern = 1) : d26 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2580 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2583 (pattern : Ten) (guard : d446 pattern = 1) : d226 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2581 pattern childGuard
    simpa only [d226, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d226, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2584 (pattern : Ten) (guard : d446 pattern = 1) : d2 pattern ≤ (1 : Int) + d10 pattern := by
  change (2 : Int) ≤ (1 : Int) + 10
  decide
theorem c2585 (pattern : Ten) (guard : d446 pattern = 1) : d15 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2575 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2584 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2586 (pattern : Ten) (guard : d446 pattern = 1) : d16 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2584 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2587 (pattern : Ten) (guard : d446 pattern = 1) : d21 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2585 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2586 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2588 (pattern : Ten) (guard : d446 pattern = 1) : d22 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2586 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2589 (pattern : Ten) (guard : d446 pattern = 1) : d25 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2587 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2588 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2590 (pattern : Ten) (guard : d446 pattern = 1) : d227 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2589 pattern childGuard
    simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2591 (pattern : Ten) (guard : d446 pattern = 1) : d230 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2583 pattern childGuard
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2590 pattern childGuard
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2592 (pattern : Ten) (guard : d446 pattern = 1) : d228 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2593 (pattern : Ten) (guard : d446 pattern = 1) : d28 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2588 pattern childGuard
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2594 (pattern : Ten) (guard : d446 pattern = 1) : d229 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2593 pattern childGuard
    simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2595 (pattern : Ten) (guard : d446 pattern = 1) : d231 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2592 pattern childGuard
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2594 pattern childGuard
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2596 (pattern : Ten) (guard : d446 pattern = 1) : d232 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2591 pattern childGuard
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2595 pattern childGuard
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2597 (pattern : Ten) (guard : d446 pattern = 1) : d233 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2595 pattern childGuard
    simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2513 pattern childGuard
    simpa only [d233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2598 (pattern : Ten) (guard : d446 pattern = 1) : d234 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d446 pattern = 1 := by simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2596 pattern childGuard
    simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d446 pattern = 1 := by simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2597 pattern childGuard
    simpa only [d234, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2599 (pattern : Ten) (guard : d360 pattern = 1) : d0 pattern ≤ (1 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2538 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2511 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2600 (pattern : Ten) (guard : d445 pattern = 1) : d0 pattern ≤ (1 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2599 pattern childGuard
    simpa only [d445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1850 pattern childGuard
    simpa only [d445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2601 (pattern : Ten) (guard : d445 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  omega
theorem c2602 (pattern : Ten) (guard : d445 pattern = 1) : d12 pattern ≤ (1 : Int) + d173 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2600 pattern childGuard
    simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2601 pattern childGuard
    simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2603 (pattern : Ten) (guard : d445 pattern = 1) : d17 pattern ≤ (1 : Int) + d176 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2600 pattern childGuard
    simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2602 pattern childGuard
    simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2604 (pattern : Ten) (guard : d445 pattern = 1) : d18 pattern ≤ (1 : Int) + d177 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2602 pattern childGuard
    simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2601 pattern childGuard
    simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2605 (pattern : Ten) (guard : d445 pattern = 1) : d23 pattern ≤ (1 : Int) + d180 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2603 pattern childGuard
    simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2604 pattern childGuard
    simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2606 (pattern : Ten) (guard : d360 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  omega
theorem c2607 (pattern : Ten) (guard : d360 pattern = 1) : d11 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2489 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2606 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2608 (pattern : Ten) (guard : d445 pattern = 1) : d11 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2607 pattern childGuard
    simpa only [d445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1658 pattern childGuard
    simpa only [d445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2609 (pattern : Ten) (guard : d445 pattern = 1) : d13 pattern ≤ (1 : Int) + d173 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d13, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2600 pattern childGuard
    simpa only [d13, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d13, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2608 pattern childGuard
    simpa only [d13, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2610 (pattern : Ten) (guard : d445 pattern = 1) : d14 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2608 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2601 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2611 (pattern : Ten) (guard : d445 pattern = 1) : d19 pattern ≤ (1 : Int) + d177 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d19, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2609 pattern childGuard
    simpa only [d19, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d19, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2610 pattern childGuard
    simpa only [d19, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2612 (pattern : Ten) (guard : d445 pattern = 1) : d20 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2610 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2601 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2613 (pattern : Ten) (guard : d445 pattern = 1) : d24 pattern ≤ (1 : Int) + d181 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d24, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2611 pattern childGuard
    simpa only [d24, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d24, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2612 pattern childGuard
    simpa only [d24, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2614 (pattern : Ten) (guard : d445 pattern = 1) : d29 pattern ≤ (1 : Int) + d184 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d29, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2605 pattern childGuard
    simpa only [d29, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d29, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2613 pattern childGuard
    simpa only [d29, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2615 (pattern : Ten) (guard : d360 pattern = 1) : d2 pattern ≤ (1 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2553 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2520 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2616 (pattern : Ten) (guard : d445 pattern = 1) : d2 pattern ≤ (1 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2615 pattern childGuard
    simpa only [d445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1869 pattern childGuard
    simpa only [d445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2617 (pattern : Ten) (guard : d445 pattern = 1) : d15 pattern ≤ (1 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2600 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2616 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2618 (pattern : Ten) (guard : d445 pattern = 1) : d16 pattern ≤ (1 : Int) + d175 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2616 pattern childGuard
    simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2601 pattern childGuard
    simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2619 (pattern : Ten) (guard : d445 pattern = 1) : d21 pattern ≤ (1 : Int) + d178 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2617 pattern childGuard
    simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2618 pattern childGuard
    simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2620 (pattern : Ten) (guard : d445 pattern = 1) : d22 pattern ≤ (1 : Int) + d179 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2618 pattern childGuard
    simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2601 pattern childGuard
    simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2621 (pattern : Ten) (guard : d445 pattern = 1) : d25 pattern ≤ (1 : Int) + d182 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2619 pattern childGuard
    simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2620 pattern childGuard
    simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2622 (pattern : Ten) (guard : d445 pattern = 1) : d30 pattern ≤ (1 : Int) + d185 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d30, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2621 pattern childGuard
    simpa only [d30, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d30, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2613 pattern childGuard
    simpa only [d30, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2623 (pattern : Ten) (guard : d445 pattern = 1) : d33 pattern ≤ (1 : Int) + d188 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d33, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2614 pattern childGuard
    simpa only [d33, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d33, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2622 pattern childGuard
    simpa only [d33, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2624 (pattern : Ten) (guard : d445 pattern = 1) : d26 pattern ≤ (1 : Int) + d181 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2604 pattern childGuard
    simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2601 pattern childGuard
    simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2625 (pattern : Ten) (guard : d445 pattern = 1) : d27 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2612 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2601 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2626 (pattern : Ten) (guard : d445 pattern = 1) : d31 pattern ≤ (1 : Int) + d186 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d31, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2624 pattern childGuard
    simpa only [d31, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d31, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2625 pattern childGuard
    simpa only [d31, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2627 (pattern : Ten) (guard : d445 pattern = 1) : d28 pattern ≤ (1 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2620 pattern childGuard
    simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2601 pattern childGuard
    simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2628 (pattern : Ten) (guard : d445 pattern = 1) : d32 pattern ≤ (1 : Int) + d187 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d32, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2627 pattern childGuard
    simpa only [d32, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d32, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2625 pattern childGuard
    simpa only [d32, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2629 (pattern : Ten) (guard : d445 pattern = 1) : d34 pattern ≤ (1 : Int) + d189 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d34, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2626 pattern childGuard
    simpa only [d34, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d34, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2628 pattern childGuard
    simpa only [d34, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2630 (pattern : Ten) (guard : d445 pattern = 1) : d35 pattern ≤ (1 : Int) + d190 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d35, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2623 pattern childGuard
    simpa only [d35, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d35, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2629 pattern childGuard
    simpa only [d35, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2631 (pattern : Ten) (guard : d445 pattern = 1) : d36 pattern ≤ (1 : Int) + d191 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d36, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2629 pattern childGuard
    simpa only [d36, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d36, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2601 pattern childGuard
    simpa only [d36, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2632 (pattern : Ten) (guard : d445 pattern = 1) : d37 pattern ≤ (1 : Int) + d192 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d445 pattern = 1 := by simpa only [d37, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2630 pattern childGuard
    simpa only [d37, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d445 pattern = 1 := by simpa only [d37, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2631 pattern childGuard
    simpa only [d37, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2633 (pattern : Ten) (guard : d360 pattern = 1) : d1 pattern ≤ (1 : Int) + d10 pattern := by
  change (1 : Int) ≤ (1 : Int) + 10
  decide
theorem c2634 (pattern : Ten) (guard : d360 pattern = 1) : d171 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2573 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2633 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2635 (pattern : Ten) (guard : d360 pattern = 1) : d173 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2634 pattern childGuard
    simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2606 pattern childGuard
    simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2636 (pattern : Ten) (guard : d360 pattern = 1) : d176 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2634 pattern childGuard
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2635 pattern childGuard
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2637 (pattern : Ten) (guard : d360 pattern = 1) : d177 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2635 pattern childGuard
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2606 pattern childGuard
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2638 (pattern : Ten) (guard : d360 pattern = 1) : d180 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2636 pattern childGuard
    simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2637 pattern childGuard
    simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2639 (pattern : Ten) (guard : d360 pattern = 1) : d181 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2637 pattern childGuard
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2606 pattern childGuard
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2640 (pattern : Ten) (guard : d360 pattern = 1) : d184 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2638 pattern childGuard
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2639 pattern childGuard
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2641 (pattern : Ten) (guard : d360 pattern = 1) : d2 pattern ≤ (1 : Int) + d10 pattern := by
  change (2 : Int) ≤ (1 : Int) + 10
  decide
theorem c2642 (pattern : Ten) (guard : d360 pattern = 1) : d3 pattern ≤ (1 : Int) + d10 pattern := by
  change (3 : Int) ≤ (1 : Int) + 10
  decide
theorem c2643 (pattern : Ten) (guard : d360 pattern = 1) : d172 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2641 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2642 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2644 (pattern : Ten) (guard : d360 pattern = 1) : d174 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2634 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2643 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2645 (pattern : Ten) (guard : d360 pattern = 1) : d175 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2643 pattern childGuard
    simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2606 pattern childGuard
    simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2646 (pattern : Ten) (guard : d360 pattern = 1) : d178 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2644 pattern childGuard
    simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2645 pattern childGuard
    simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2647 (pattern : Ten) (guard : d360 pattern = 1) : d179 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2645 pattern childGuard
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2606 pattern childGuard
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2648 (pattern : Ten) (guard : d360 pattern = 1) : d182 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2646 pattern childGuard
    simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2647 pattern childGuard
    simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2649 (pattern : Ten) (guard : d360 pattern = 1) : d185 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2648 pattern childGuard
    simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2639 pattern childGuard
    simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2650 (pattern : Ten) (guard : d360 pattern = 1) : d188 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2640 pattern childGuard
    simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2649 pattern childGuard
    simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2651 (pattern : Ten) (guard : d360 pattern = 1) : d186 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2639 pattern childGuard
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2606 pattern childGuard
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2652 (pattern : Ten) (guard : d360 pattern = 1) : d183 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2647 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2606 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2653 (pattern : Ten) (guard : d360 pattern = 1) : d187 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2652 pattern childGuard
    simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2606 pattern childGuard
    simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2654 (pattern : Ten) (guard : d360 pattern = 1) : d189 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2651 pattern childGuard
    simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2653 pattern childGuard
    simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2655 (pattern : Ten) (guard : d360 pattern = 1) : d190 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2650 pattern childGuard
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2654 pattern childGuard
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2656 (pattern : Ten) (guard : d360 pattern = 1) : d191 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2654 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2606 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2657 (pattern : Ten) (guard : d360 pattern = 1) : d192 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d360 pattern = 1 := by simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2655 pattern childGuard
    simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d360 pattern = 1 := by simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2656 pattern childGuard
    simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2658 (pattern : Ten) (guard : d357 pattern = 1) : d37 pattern ≤ (2 : Int) + d37 pattern := by
  omega
theorem c2659 (pattern : Ten) (guard : d356 pattern = 1) : d192 pattern ≤ (2 : Int) + d192 pattern := by
  omega
theorem c2660 (pattern : Ten) (guard : d350 pattern = 1) : d37 pattern ≤ (2 : Int) + d37 pattern := by
  omega
theorem c2661 (pattern : Ten) (guard : d1 pattern = 1) : d192 pattern ≤ (2 : Int) + d192 pattern := by
  omega
theorem c2662 (pattern : Ten) (guard : d384 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c2663 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) ≤ (0 : Int) + 10
  decide
theorem c2664 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2665 (pattern : Ten) (guard : d384 pattern = 1) : d12 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2663 pattern childGuard
    simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d384, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2666 (pattern : Ten) (guard : d384 pattern = 1) : d17 pattern ≤ (0 : Int) + d88 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d17, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2662 pattern childGuard
    simpa only [d17, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d17, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2665 pattern childGuard
    simpa only [d17, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2667 (pattern : Ten) (guard : d384 pattern = 1) : d18 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2665 pattern childGuard
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2668 (pattern : Ten) (guard : d384 pattern = 1) : d23 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d23, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2666 pattern childGuard
    simpa only [d23, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d23, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2667 pattern childGuard
    simpa only [d23, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2669 (pattern : Ten) (guard : d0 pattern = 1) : d11 pattern ≤ (0 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2670 (pattern : Ten) (guard : d384 pattern = 1) : d13 pattern ≤ (0 : Int) + d11 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2338 pattern childGuard
    simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2669 pattern childGuard
    simpa only [d384, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2671 (pattern : Ten) (guard : d384 pattern = 1) : d14 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2128 pattern childGuard
    simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d384, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2672 (pattern : Ten) (guard : d384 pattern = 1) : d19 pattern ≤ (0 : Int) + d90 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d19, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2670 pattern childGuard
    simpa only [d19, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d19, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2671 pattern childGuard
    simpa only [d19, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2673 (pattern : Ten) (guard : d384 pattern = 1) : d20 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2671 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2674 (pattern : Ten) (guard : d384 pattern = 1) : d24 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d24, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2672 pattern childGuard
    simpa only [d24, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d24, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2673 pattern childGuard
    simpa only [d24, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2675 (pattern : Ten) (guard : d384 pattern = 1) : d29 pattern ≤ (0 : Int) + d101 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d29, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2668 pattern childGuard
    simpa only [d29, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d29, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2674 pattern childGuard
    simpa only [d29, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2676 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem c2677 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2678 (pattern : Ten) (guard : d384 pattern = 1) : d15 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2676 pattern childGuard
    simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2677 pattern childGuard
    simpa only [d384, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2679 (pattern : Ten) (guard : d384 pattern = 1) : d16 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2116 pattern childGuard
    simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d384, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2680 (pattern : Ten) (guard : d384 pattern = 1) : d21 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d21, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2678 pattern childGuard
    simpa only [d21, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d21, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2679 pattern childGuard
    simpa only [d21, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2681 (pattern : Ten) (guard : d384 pattern = 1) : d22 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2679 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2682 (pattern : Ten) (guard : d384 pattern = 1) : d25 pattern ≤ (0 : Int) + d98 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d25, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2680 pattern childGuard
    simpa only [d25, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d25, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2681 pattern childGuard
    simpa only [d25, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2683 (pattern : Ten) (guard : d384 pattern = 1) : d30 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d30, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2682 pattern childGuard
    simpa only [d30, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d30, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2674 pattern childGuard
    simpa only [d30, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2684 (pattern : Ten) (guard : d384 pattern = 1) : d33 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d33, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2675 pattern childGuard
    simpa only [d33, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d33, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2683 pattern childGuard
    simpa only [d33, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2685 (pattern : Ten) (guard : d384 pattern = 1) : d26 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2667 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2686 (pattern : Ten) (guard : d384 pattern = 1) : d27 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2673 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2687 (pattern : Ten) (guard : d384 pattern = 1) : d31 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2685 pattern childGuard
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2686 pattern childGuard
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2688 (pattern : Ten) (guard : d384 pattern = 1) : d28 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2681 pattern childGuard
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2689 (pattern : Ten) (guard : d384 pattern = 1) : d32 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2688 pattern childGuard
    simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2686 pattern childGuard
    simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2690 (pattern : Ten) (guard : d384 pattern = 1) : d34 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2687 pattern childGuard
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2689 pattern childGuard
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2691 (pattern : Ten) (guard : d384 pattern = 1) : d35 pattern ≤ (0 : Int) + d106 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d35, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2684 pattern childGuard
    simpa only [d35, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d35, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2690 pattern childGuard
    simpa only [d35, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2692 (pattern : Ten) (guard : d384 pattern = 1) : d36 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2690 pattern childGuard
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2693 (pattern : Ten) (guard : d384 pattern = 1) : d37 pattern ≤ (0 : Int) + d448 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d384 pattern = 1 := by simpa only [d37, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2691 pattern childGuard
    simpa only [d37, d448, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d384 pattern = 1 := by simpa only [d37, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2692 pattern childGuard
    simpa only [d37, d448, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2694 (pattern : Ten) (guard : d383 pattern = 1) : d171 pattern ≤ (0 : Int) + d171 pattern := by
  omega
theorem c2695 (pattern : Ten) (guard : d383 pattern = 1) : d173 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2359 pattern childGuard
    simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d383, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2696 (pattern : Ten) (guard : d383 pattern = 1) : d176 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d176, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2694 pattern childGuard
    simpa only [d176, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d176, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2695 pattern childGuard
    simpa only [d176, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2697 (pattern : Ten) (guard : d383 pattern = 1) : d177 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2695 pattern childGuard
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2698 (pattern : Ten) (guard : d383 pattern = 1) : d180 pattern ≤ (0 : Int) + d254 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d180, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2696 pattern childGuard
    simpa only [d180, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d180, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2697 pattern childGuard
    simpa only [d180, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2699 (pattern : Ten) (guard : d383 pattern = 1) : d181 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2697 pattern childGuard
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2700 (pattern : Ten) (guard : d383 pattern = 1) : d184 pattern ≤ (0 : Int) + d259 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d184, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2698 pattern childGuard
    simpa only [d184, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d184, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2699 pattern childGuard
    simpa only [d184, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2701 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem c2702 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (0 : Int) + d3 pattern := by
  change (1 : Int) ≤ (0 : Int) + 3
  decide
theorem c2703 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (0 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2701 pattern childGuard
    simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2702 pattern childGuard
    simpa only [d171, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2704 (pattern : Ten) (guard : d0 pattern = 1) : d172 pattern ≤ (0 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2705 (pattern : Ten) (guard : d383 pattern = 1) : d174 pattern ≤ (0 : Int) + d172 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2703 pattern childGuard
    simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2704 pattern childGuard
    simpa only [d383, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2706 (pattern : Ten) (guard : d383 pattern = 1) : d175 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2153 pattern childGuard
    simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d383, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2707 (pattern : Ten) (guard : d383 pattern = 1) : d178 pattern ≤ (0 : Int) + d252 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d178, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2705 pattern childGuard
    simpa only [d178, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d178, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2706 pattern childGuard
    simpa only [d178, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2708 (pattern : Ten) (guard : d383 pattern = 1) : d179 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2706 pattern childGuard
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2709 (pattern : Ten) (guard : d383 pattern = 1) : d182 pattern ≤ (0 : Int) + d256 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d182, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2707 pattern childGuard
    simpa only [d182, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d182, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2708 pattern childGuard
    simpa only [d182, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2710 (pattern : Ten) (guard : d383 pattern = 1) : d185 pattern ≤ (0 : Int) + d260 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d185, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2709 pattern childGuard
    simpa only [d185, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d185, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2699 pattern childGuard
    simpa only [d185, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2711 (pattern : Ten) (guard : d383 pattern = 1) : d188 pattern ≤ (0 : Int) + d262 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d188, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2700 pattern childGuard
    simpa only [d188, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d188, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2710 pattern childGuard
    simpa only [d188, d262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2712 (pattern : Ten) (guard : d383 pattern = 1) : d186 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2699 pattern childGuard
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2713 (pattern : Ten) (guard : d383 pattern = 1) : d183 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2708 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2714 (pattern : Ten) (guard : d383 pattern = 1) : d187 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2713 pattern childGuard
    simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2715 (pattern : Ten) (guard : d383 pattern = 1) : d189 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2712 pattern childGuard
    simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2714 pattern childGuard
    simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2716 (pattern : Ten) (guard : d383 pattern = 1) : d190 pattern ≤ (0 : Int) + d264 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d190, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2711 pattern childGuard
    simpa only [d190, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d190, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2715 pattern childGuard
    simpa only [d190, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2717 (pattern : Ten) (guard : d383 pattern = 1) : d191 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2715 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2718 (pattern : Ten) (guard : d383 pattern = 1) : d192 pattern ≤ (0 : Int) + d449 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d383 pattern = 1 := by simpa only [d192, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2716 pattern childGuard
    simpa only [d192, d449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d383 pattern = 1 := by simpa only [d192, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2717 pattern childGuard
    simpa only [d192, d449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2719 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (2 : Int) + d0 pattern := by
  omega
end NetHack.Sokoban41.Diagram
