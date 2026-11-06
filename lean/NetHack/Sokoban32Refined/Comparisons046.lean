/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons045
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6440 (p : Pattern) (guard : d1148 p = 1) : d610 p ≤ (0 : Int) + d271 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6437 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6439 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6441 (p : Pattern) (guard : d1148 p = 1) : d611 p ≤ (0 : Int) + d272 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d611, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6429 p hg
    simpa only [d611, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d611, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6440 p hg
    simpa only [d611, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6442 (p : Pattern) (guard : d873 p = 1) : d583 p ≤ (0 : Int) + d8 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6376 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6378 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6443 (p : Pattern) (guard : d873 p = 1) : d603 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d603, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6442 p hg
    simpa only [d603, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d603, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6399 p hg
    simpa only [d603, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6444 (p : Pattern) (guard : d873 p = 1) : d612 p ≤ (0 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6443 p hg
    simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6422 p hg
    simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6445 (p : Pattern) (guard : d873 p = 1) : d613 p ≤ (0 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d613, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6444 p hg
    simpa only [d613, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d613, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6425 p hg
    simpa only [d613, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6446 (p : Pattern) (guard : d0 p = 1) : d614 p ≤ (0 : Int) + d160 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6447 (p : Pattern) (guard : d1148 p = 1) : d615 p ≤ (0 : Int) + d273 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d615, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6445 p hg
    simpa only [d1148, d615, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d615, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6446 p hg
    simpa only [d1148, d615, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6448 (p : Pattern) (guard : d1148 p = 1) : d616 p ≤ (0 : Int) + d274 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d616, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d616, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d616, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6447 p hg
    simpa only [d616, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6449 (p : Pattern) (guard : d0 p = 1) : d617 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6450 (p : Pattern) (guard : d1148 p = 1) : d618 p ≤ (0 : Int) + d270 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d618, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6435 p hg
    simpa only [d1148, d618, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d618, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6449 p hg
    simpa only [d1148, d618, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6451 (p : Pattern) (guard : d873 p = 1) : d586 p ≤ (0 : Int) + d109 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d586, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6430 p hg
    simpa only [d586, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d586, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6432 p hg
    simpa only [d586, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6452 (p : Pattern) (guard : d873 p = 1) : d619 p ≤ (0 : Int) + d110 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d619, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6430 p hg
    simpa only [d619, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d619, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6451 p hg
    simpa only [d619, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6453 (p : Pattern) (guard : d0 p = 1) : d620 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6454 (p : Pattern) (guard : d1148 p = 1) : d621 p ≤ (0 : Int) + d275 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d621, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6452 p hg
    simpa only [d1148, d621, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d621, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6453 p hg
    simpa only [d1148, d621, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6455 (p : Pattern) (guard : d1148 p = 1) : d622 p ≤ (0 : Int) + d276 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d622, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6450 p hg
    simpa only [d622, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d622, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6454 p hg
    simpa only [d622, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6456 (p : Pattern) (guard : d1148 p = 1) : d623 p ≤ (0 : Int) + d277 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d623, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6448 p hg
    simpa only [d623, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d623, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6455 p hg
    simpa only [d623, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6457 (p : Pattern) (guard : d1148 p = 1) : d624 p ≤ (0 : Int) + d278 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d624, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6441 p hg
    simpa only [d624, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d624, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6456 p hg
    simpa only [d624, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6458 (p : Pattern) (guard : d1148 p = 1) : d625 p ≤ (0 : Int) + d279 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d625, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6420 p hg
    simpa only [d625, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d625, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6457 p hg
    simpa only [d625, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6459 (p : Pattern) (guard : d0 p = 1) : d627 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6460 (p : Pattern) (guard : d1148 p = 1) : d628 p ≤ (0 : Int) + d261 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d628, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6392 p hg
    simpa only [d1148, d628, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d628, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6459 p hg
    simpa only [d1148, d628, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6461 (p : Pattern) (guard : d1148 p = 1) : d629 p ≤ (0 : Int) + d262 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d629, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6394 p hg
    simpa only [d629, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d629, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6460 p hg
    simpa only [d629, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6462 (p : Pattern) (guard : d0 p = 1) : d571 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6463 (p : Pattern) (guard : d1148 p = 1) : d572 p ≤ (0 : Int) + d263 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d572, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6404 p hg
    simpa only [d1148, d572, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d572, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6462 p hg
    simpa only [d1148, d572, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6464 (p : Pattern) (guard : d1148 p = 1) : d573 p ≤ (0 : Int) + d264 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d573, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6398 p hg
    simpa only [d573, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d573, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6463 p hg
    simpa only [d573, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6465 (p : Pattern) (guard : d1148 p = 1) : d630 p ≤ (0 : Int) + d265 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d630, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6461 p hg
    simpa only [d630, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d630, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6464 p hg
    simpa only [d630, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6466 (p : Pattern) (guard : d873 p = 1) : d584 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d584, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6442 p hg
    simpa only [d584, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d584, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6381 p hg
    simpa only [d584, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6467 (p : Pattern) (guard : d873 p = 1) : d631 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6466 p hg
    simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6383 p hg
    simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6468 (p : Pattern) (guard : d873 p = 1) : d632 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d632, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6467 p hg
    simpa only [d632, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d632, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6391 p hg
    simpa only [d632, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6469 (p : Pattern) (guard : d0 p = 1) : d633 p ≤ (0 : Int) + d160 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6470 (p : Pattern) (guard : d1148 p = 1) : d634 p ≤ (0 : Int) + d280 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d634, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6468 p hg
    simpa only [d1148, d634, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d634, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6469 p hg
    simpa only [d1148, d634, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6471 (p : Pattern) (guard : d1148 p = 1) : d635 p ≤ (0 : Int) + d281 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d635, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d635, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d635, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6470 p hg
    simpa only [d635, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6472 (p : Pattern) (guard : d0 p = 1) : d590 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6473 (p : Pattern) (guard : d1148 p = 1) : d591 p ≤ (0 : Int) + d282 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d591, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6396 p hg
    simpa only [d1148, d591, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d591, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6472 p hg
    simpa only [d1148, d591, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6474 (p : Pattern) (guard : d0 p = 1) : d592 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6475 (p : Pattern) (guard : d1148 p = 1) : d593 p ≤ (0 : Int) + d283 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d593, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6404 p hg
    simpa only [d1148, d593, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d593, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6474 p hg
    simpa only [d1148, d593, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6476 (p : Pattern) (guard : d1148 p = 1) : d594 p ≤ (0 : Int) + d284 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d594, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6473 p hg
    simpa only [d594, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d594, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6475 p hg
    simpa only [d594, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6477 (p : Pattern) (guard : d1148 p = 1) : d636 p ≤ (0 : Int) + d285 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d636, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6471 p hg
    simpa only [d636, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d636, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6476 p hg
    simpa only [d636, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6478 (p : Pattern) (guard : d1148 p = 1) : d637 p ≤ (0 : Int) + d286 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d637, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6465 p hg
    simpa only [d637, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d637, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6477 p hg
    simpa only [d637, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6479 (p : Pattern) (guard : d0 p = 1) : d641 p ≤ (0 : Int) + d160 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6480 (p : Pattern) (guard : d1148 p = 1) : d642 p ≤ (0 : Int) + d273 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d642, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6445 p hg
    simpa only [d1148, d642, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d642, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6479 p hg
    simpa only [d1148, d642, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6481 (p : Pattern) (guard : d1148 p = 1) : d643 p ≤ (0 : Int) + d274 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d643, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6460 p hg
    simpa only [d643, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d643, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6480 p hg
    simpa only [d643, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6482 (p : Pattern) (guard : d0 p = 1) : d586 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6483 (p : Pattern) (guard : d1148 p = 1) : d644 p ≤ (0 : Int) + d275 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d644, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6452 p hg
    simpa only [d1148, d644, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d644, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6482 p hg
    simpa only [d1148, d644, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6484 (p : Pattern) (guard : d1148 p = 1) : d645 p ≤ (0 : Int) + d276 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d645, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6439 p hg
    simpa only [d645, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d645, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6483 p hg
    simpa only [d645, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6485 (p : Pattern) (guard : d1148 p = 1) : d646 p ≤ (0 : Int) + d277 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d646, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6481 p hg
    simpa only [d646, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d646, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d646, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6486 (p : Pattern) (guard : d1148 p = 1) : d647 p ≤ (0 : Int) + d287 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d647, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6470 p hg
    simpa only [d647, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d647, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6475 p hg
    simpa only [d647, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6487 (p : Pattern) (guard : d1148 p = 1) : d648 p ≤ (0 : Int) + d288 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d648, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6454 p hg
    simpa only [d648, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d648, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2626 p hg
    simpa only [d648, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6488 (p : Pattern) (guard : d1148 p = 1) : d649 p ≤ (0 : Int) + d289 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d649, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6486 p hg
    simpa only [d649, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d649, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6487 p hg
    simpa only [d649, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6489 (p : Pattern) (guard : d1148 p = 1) : d650 p ≤ (0 : Int) + d290 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d650, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6485 p hg
    simpa only [d650, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d650, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6488 p hg
    simpa only [d650, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6490 (p : Pattern) (guard : d1148 p = 1) : d651 p ≤ (0 : Int) + d291 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d651, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6478 p hg
    simpa only [d651, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d651, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6489 p hg
    simpa only [d651, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6491 (p : Pattern) (guard : d1148 p = 1) : d652 p ≤ (0 : Int) + d292 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d652, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6458 p hg
    simpa only [d652, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d652, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6490 p hg
    simpa only [d652, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6492 (p : Pattern) (guard : d0 p = 1) : d550 p ≤ (1 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6493 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (1 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6494 (p : Pattern) (guard : d873 p = 1) : d538 p ≤ (1 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d538, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare323 p hg
    simpa only [d873, d538, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d538, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6493 p hg
    simpa only [d873, d538, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6495 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (1 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6496 (p : Pattern) (guard : d873 p = 1) : d539 p ≤ (1 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d539, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare323 p hg
    simpa only [d873, d539, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d539, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6495 p hg
    simpa only [d873, d539, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6497 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (1 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6498 (p : Pattern) (guard : d873 p = 1) : d540 p ≤ (1 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d540, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare327 p hg
    simpa only [d873, d540, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d540, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6497 p hg
    simpa only [d873, d540, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6499 (p : Pattern) (guard : d873 p = 1) : d541 p ≤ (1 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d541, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6496 p hg
    simpa only [d541, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d541, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6498 p hg
    simpa only [d541, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6500 (p : Pattern) (guard : d873 p = 1) : d542 p ≤ (1 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d542, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6494 p hg
    simpa only [d542, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d542, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6499 p hg
    simpa only [d542, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6501 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (1 : Int) + d0 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1365 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6502 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (1 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6501 p hg
    simpa only [d30, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d30, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6503 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (1 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36 p hg
    simpa only [d31, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6502 p hg
    simpa only [d31, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6504 (p : Pattern) (guard : d873 p = 1) : d551 p ≤ (1 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d551, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6503 p hg
    simpa only [d873, d551, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d551, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6495 p hg
    simpa only [d873, d551, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6505 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (1 : Int) + d1 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare313 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare381 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6506 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (1 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6505 p hg
    simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6507 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare312 p hg
    simpa only [d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6506 p hg
    simpa only [d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6508 (p : Pattern) (guard : d873 p = 1) : d546 p ≤ (1 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d546, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6507 p hg
    simpa only [d873, d546, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d546, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6497 p hg
    simpa only [d873, d546, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6509 (p : Pattern) (guard : d873 p = 1) : d552 p ≤ (1 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d552, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6504 p hg
    simpa only [d552, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d552, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6508 p hg
    simpa only [d552, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6510 (p : Pattern) (guard : d873 p = 1) : d553 p ≤ (1 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d553, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6504 p hg
    simpa only [d553, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d553, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6509 p hg
    simpa only [d553, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6511 (p : Pattern) (guard : d873 p = 1) : d554 p ≤ (1 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6500 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6510 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6512 (p : Pattern) (guard : d873 p = 1) : d543 p ≤ (1 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d543, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6496 p hg
    simpa only [d543, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d543, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6499 p hg
    simpa only [d543, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6513 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (1 : Int) + d18 p := by
  omega
theorem compare6514 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (1 : Int) + d19 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6515 (p : Pattern) (guard : d873 p = 1) : d545 p ≤ (1 : Int) + d20 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d545, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6513 p hg
    simpa only [d873, d545, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d545, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6514 p hg
    simpa only [d873, d545, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6516 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (1 : Int) + d22 p := by
  omega
theorem compare6517 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (1 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6518 (p : Pattern) (guard : d873 p = 1) : d546 p ≤ (1 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d546, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6516 p hg
    simpa only [d873, d546, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d546, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6517 p hg
    simpa only [d873, d546, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6519 (p : Pattern) (guard : d873 p = 1) : d547 p ≤ (1 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d547, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6515 p hg
    simpa only [d547, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d547, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6518 p hg
    simpa only [d547, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6520 (p : Pattern) (guard : d873 p = 1) : d548 p ≤ (1 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d548, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6515 p hg
    simpa only [d548, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d548, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6519 p hg
    simpa only [d548, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6521 (p : Pattern) (guard : d873 p = 1) : d549 p ≤ (1 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d549, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6512 p hg
    simpa only [d549, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d549, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6520 p hg
    simpa only [d549, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6522 (p : Pattern) (guard : d873 p = 1) : d555 p ≤ (1 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d555, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6511 p hg
    simpa only [d555, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d555, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6521 p hg
    simpa only [d555, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6523 (p : Pattern) (guard : d874 p = 1) : d556 p ≤ (1 : Int) + d28 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6492 p hg
    simpa only [d874, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6522 p hg
    simpa only [d874, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6524 (p : Pattern) (guard : d0 p = 1) : d558 p ≤ (1 : Int) + d47 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6525 (p : Pattern) (guard : d873 p = 1) : d559 p ≤ (1 : Int) + d15 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6499 p hg
    simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6509 p hg
    simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6526 (p : Pattern) (guard : d873 p = 1) : d557 p ≤ (1 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d557, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6499 p hg
    simpa only [d557, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d557, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6519 p hg
    simpa only [d557, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6527 (p : Pattern) (guard : d873 p = 1) : d560 p ≤ (1 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d560, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6525 p hg
    simpa only [d560, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d560, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6526 p hg
    simpa only [d560, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6528 (p : Pattern) (guard : d874 p = 1) : d561 p ≤ (1 : Int) + d47 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6524 p hg
    simpa only [d874, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6527 p hg
    simpa only [d874, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6529 (p : Pattern) (guard : d0 p = 1) : d567 p ≤ (1 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6530 (p : Pattern) (guard : d873 p = 1) : d2 p ≤ (1 : Int) + d2 p := by
  omega
theorem compare6531 (p : Pattern) (guard : d873 p = 1) : d562 p ≤ (1 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d562, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6496 p hg
    simpa only [d562, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d562, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6530 p hg
    simpa only [d562, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6532 (p : Pattern) (guard : d873 p = 1) : d563 p ≤ (1 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d563, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6499 p hg
    simpa only [d563, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d563, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6531 p hg
    simpa only [d563, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6533 (p : Pattern) (guard : d873 p = 1) : d568 p ≤ (1 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d568, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6504 p hg
    simpa only [d568, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d568, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6530 p hg
    simpa only [d568, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6534 (p : Pattern) (guard : d873 p = 1) : d569 p ≤ (1 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d569, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6509 p hg
    simpa only [d569, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d569, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6533 p hg
    simpa only [d569, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6535 (p : Pattern) (guard : d873 p = 1) : d570 p ≤ (1 : Int) + d53 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6532 p hg
    simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6534 p hg
    simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6536 (p : Pattern) (guard : d873 p = 1) : d564 p ≤ (1 : Int) + d54 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d564, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6515 p hg
    simpa only [d564, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d564, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6530 p hg
    simpa only [d564, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6537 (p : Pattern) (guard : d873 p = 1) : d565 p ≤ (1 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d565, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6519 p hg
    simpa only [d565, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d565, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6536 p hg
    simpa only [d565, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6538 (p : Pattern) (guard : d873 p = 1) : d566 p ≤ (1 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d566, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6532 p hg
    simpa only [d566, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d566, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6537 p hg
    simpa only [d566, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6539 (p : Pattern) (guard : d873 p = 1) : d571 p ≤ (1 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d571, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6535 p hg
    simpa only [d571, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d571, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6538 p hg
    simpa only [d571, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6540 (p : Pattern) (guard : d874 p = 1) : d572 p ≤ (1 : Int) + d57 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d874, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6539 p hg
    simpa only [d874, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6541 (p : Pattern) (guard : d874 p = 1) : d573 p ≤ (1 : Int) + d1223 p := by
  cases selected : p 113 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d573, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6528 p hg
    simpa only [d573, d1223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d573, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6540 p hg
    simpa only [d573, d1223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6542 (p : Pattern) (guard : d874 p = 1) : d574 p ≤ (1 : Int) + d1224 p := by
  cases selected : p 112 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d574, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6523 p hg
    simpa only [d574, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d574, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6541 p hg
    simpa only [d574, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6543 (p : Pattern) (guard : d0 p = 1) : d595 p ≤ (1 : Int) + d1224 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6544 (p : Pattern) (guard : d875 p = 1) : d596 p ≤ (1 : Int) + d1224 p := by
  cases selected : p 106 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d875, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6542 p hg
    simpa only [d875, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d875, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6543 p hg
    simpa only [d875, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6545 (p : Pattern) (guard : d0 p = 1) : d602 p ≤ (1 : Int) + d89 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6546 (p : Pattern) (guard : d873 p = 1) : d583 p ≤ (1 : Int) + d8 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6494 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6496 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6547 (p : Pattern) (guard : d873 p = 1) : d603 p ≤ (1 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d603, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6546 p hg
    simpa only [d603, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d603, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6531 p hg
    simpa only [d603, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6548 (p : Pattern) (guard : d873 p = 1) : d604 p ≤ (1 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d604, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6504 p hg
    simpa only [d604, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d604, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6533 p hg
    simpa only [d604, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6549 (p : Pattern) (guard : d873 p = 1) : d605 p ≤ (1 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6547 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6548 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6550 (p : Pattern) (guard : d873 p = 1) : d598 p ≤ (1 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d598, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6496 p hg
    simpa only [d598, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d598, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6531 p hg
    simpa only [d598, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6551 (p : Pattern) (guard : d873 p = 1) : d600 p ≤ (1 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d600, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6515 p hg
    simpa only [d600, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d600, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6536 p hg
    simpa only [d600, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6552 (p : Pattern) (guard : d873 p = 1) : d601 p ≤ (1 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d601, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6550 p hg
    simpa only [d601, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d601, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6551 p hg
    simpa only [d601, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6553 (p : Pattern) (guard : d873 p = 1) : d606 p ≤ (1 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d606, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6549 p hg
    simpa only [d606, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d606, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6552 p hg
    simpa only [d606, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6554 (p : Pattern) (guard : d874 p = 1) : d607 p ≤ (1 : Int) + d89 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6545 p hg
    simpa only [d874, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6553 p hg
    simpa only [d874, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6555 (p : Pattern) (guard : d874 p = 1) : d608 p ≤ (1 : Int) + d1225 p := by
  cases selected : p 113 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d608, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6523 p hg
    simpa only [d608, d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d608, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6554 p hg
    simpa only [d608, d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6556 (p : Pattern) (guard : d0 p = 1) : d609 p ≤ (1 : Int) + d100 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6557 (p : Pattern) (guard : d873 p = 1) : d576 p ≤ (1 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d576, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6498 p hg
    simpa only [d576, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d576, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6530 p hg
    simpa only [d576, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6558 (p : Pattern) (guard : d873 p = 1) : d577 p ≤ (1 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d577, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6498 p hg
    simpa only [d577, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d577, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6557 p hg
    simpa only [d577, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6559 (p : Pattern) (guard : d873 p = 1) : d578 p ≤ (1 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d578, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6508 p hg
    simpa only [d578, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d578, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6530 p hg
    simpa only [d578, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6560 (p : Pattern) (guard : d873 p = 1) : d579 p ≤ (1 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d579, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6508 p hg
    simpa only [d579, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d579, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6559 p hg
    simpa only [d579, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6561 (p : Pattern) (guard : d873 p = 1) : d580 p ≤ (1 : Int) + d98 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6558 p hg
    simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6560 p hg
    simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6562 (p : Pattern) (guard : d873 p = 1) : d578 p ≤ (1 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d578, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6518 p hg
    simpa only [d578, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d578, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6530 p hg
    simpa only [d578, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6563 (p : Pattern) (guard : d873 p = 1) : d579 p ≤ (1 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d579, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6518 p hg
    simpa only [d579, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d579, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6562 p hg
    simpa only [d579, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6564 (p : Pattern) (guard : d873 p = 1) : d580 p ≤ (1 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d580, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6558 p hg
    simpa only [d580, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d580, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6563 p hg
    simpa only [d580, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6565 (p : Pattern) (guard : d873 p = 1) : d580 p ≤ (1 : Int) + d100 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6561 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6564 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6566 (p : Pattern) (guard : d874 p = 1) : d610 p ≤ (1 : Int) + d100 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6556 p hg
    simpa only [d874, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6565 p hg
    simpa only [d874, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6567 (p : Pattern) (guard : d0 p = 1) : d609 p ≤ (1 : Int) + d110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6568 (p : Pattern) (guard : d873 p = 1) : d540 p ≤ (1 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10 p hg
    simpa only [d873, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1963 p hg
    simpa only [d873, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6569 (p : Pattern) (guard : d873 p = 1) : d540 p ≤ (1 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6498 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6568 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6570 (p : Pattern) (guard : d873 p = 1) : d577 p ≤ (1 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6569 p hg
    simpa only [d577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6557 p hg
    simpa only [d577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6571 (p : Pattern) (guard : d873 p = 1) : d546 p ≤ (1 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18 p hg
    simpa only [d873, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1963 p hg
    simpa only [d873, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6572 (p : Pattern) (guard : d873 p = 1) : d546 p ≤ (1 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6508 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6571 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6573 (p : Pattern) (guard : d873 p = 1) : d579 p ≤ (1 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6572 p hg
    simpa only [d579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6559 p hg
    simpa only [d579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6574 (p : Pattern) (guard : d873 p = 1) : d580 p ≤ (1 : Int) + d97 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6570 p hg
    simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6573 p hg
    simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6575 (p : Pattern) (guard : d873 p = 1) : d546 p ≤ (1 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6518 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6571 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6576 (p : Pattern) (guard : d873 p = 1) : d579 p ≤ (1 : Int) + d70 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6575 p hg
    simpa only [d579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6562 p hg
    simpa only [d579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6577 (p : Pattern) (guard : d873 p = 1) : d580 p ≤ (1 : Int) + d109 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d580, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6570 p hg
    simpa only [d580, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d580, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6576 p hg
    simpa only [d580, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6578 (p : Pattern) (guard : d873 p = 1) : d580 p ≤ (1 : Int) + d110 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6574 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6577 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6579 (p : Pattern) (guard : d874 p = 1) : d610 p ≤ (1 : Int) + d110 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6567 p hg
    simpa only [d874, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6578 p hg
    simpa only [d874, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
