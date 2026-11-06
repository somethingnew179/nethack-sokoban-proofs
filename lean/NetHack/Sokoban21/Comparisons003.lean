/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons002
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c420 (pattern : Twelve) (guard : d1837 pattern = 1) : d1663 pattern ≤ (0 : Int) + d1703 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1663, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c418 pattern childGuard
    simpa only [d1663, d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1663, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c419 pattern childGuard
    simpa only [d1663, d1703, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c421 (pattern : Twelve) (guard : d1837 pattern = 1) : d1664 pattern ≤ (0 : Int) + d1704 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1664, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c402 pattern childGuard
    simpa only [d1664, d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1664, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c420 pattern childGuard
    simpa only [d1664, d1704, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c422 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (0 : Int) + d72 pattern := by
  omega
theorem c423 (pattern : Twelve) (guard : d0 pattern = 1) : d73 pattern ≤ (0 : Int) + d198 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c424 (pattern : Twelve) (guard : d1839 pattern = 1) : d91 pattern ≤ (0 : Int) + d304 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d91, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c422 pattern childGuard
    simpa only [d1839, d91, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d91, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c423 pattern childGuard
    simpa only [d1839, d91, d304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c425 (pattern : Twelve) (guard : d1 pattern = 1) : d74 pattern ≤ (0 : Int) + d74 pattern := by
  omega
theorem c426 (pattern : Twelve) (guard : d0 pattern = 1) : d75 pattern ≤ (0 : Int) + d200 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c427 (pattern : Twelve) (guard : d1839 pattern = 1) : d92 pattern ≤ (0 : Int) + d305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d92, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c425 pattern childGuard
    simpa only [d1839, d92, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d92, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c426 pattern childGuard
    simpa only [d1839, d92, d305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c428 (pattern : Twelve) (guard : d1839 pattern = 1) : d102 pattern ≤ (0 : Int) + d320 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d102, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c424 pattern childGuard
    simpa only [d102, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d102, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c427 pattern childGuard
    simpa only [d102, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c429 (pattern : Twelve) (guard : d0 pattern = 1) : d76 pattern ≤ (0 : Int) + d200 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c430 (pattern : Twelve) (guard : d1839 pattern = 1) : d93 pattern ≤ (0 : Int) + d306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d93, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c422 pattern childGuard
    simpa only [d1839, d93, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d93, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c429 pattern childGuard
    simpa only [d1839, d93, d306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c431 (pattern : Twelve) (guard : d1 pattern = 1) : d77 pattern ≤ (0 : Int) + d77 pattern := by
  omega
theorem c432 (pattern : Twelve) (guard : d0 pattern = 1) : d78 pattern ≤ (0 : Int) + d202 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c433 (pattern : Twelve) (guard : d1839 pattern = 1) : d94 pattern ≤ (0 : Int) + d307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d94, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c431 pattern childGuard
    simpa only [d1839, d94, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d94, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c432 pattern childGuard
    simpa only [d1839, d94, d307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c434 (pattern : Twelve) (guard : d1839 pattern = 1) : d103 pattern ≤ (0 : Int) + d321 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d103, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c430 pattern childGuard
    simpa only [d103, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d103, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c433 pattern childGuard
    simpa only [d103, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c435 (pattern : Twelve) (guard : d1839 pattern = 1) : d110 pattern ≤ (0 : Int) + d332 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d110, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c428 pattern childGuard
    simpa only [d110, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d110, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c434 pattern childGuard
    simpa only [d110, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c436 (pattern : Twelve) (guard : d1 pattern = 1) : d79 pattern ≤ (0 : Int) + d79 pattern := by
  omega
theorem c437 (pattern : Twelve) (guard : d0 pattern = 1) : d80 pattern ≤ (0 : Int) + d204 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c438 (pattern : Twelve) (guard : d1839 pattern = 1) : d95 pattern ≤ (0 : Int) + d308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d95, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c436 pattern childGuard
    simpa only [d1839, d95, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d95, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c437 pattern childGuard
    simpa only [d1839, d95, d308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c439 (pattern : Twelve) (guard : d1 pattern = 1) : d81 pattern ≤ (0 : Int) + d81 pattern := by
  omega
theorem c440 (pattern : Twelve) (guard : d0 pattern = 1) : d82 pattern ≤ (0 : Int) + d206 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c441 (pattern : Twelve) (guard : d1839 pattern = 1) : d96 pattern ≤ (0 : Int) + d309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d96, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c439 pattern childGuard
    simpa only [d1839, d96, d309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d96, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c440 pattern childGuard
    simpa only [d1839, d96, d309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c442 (pattern : Twelve) (guard : d1839 pattern = 1) : d104 pattern ≤ (0 : Int) + d322 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d104, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c438 pattern childGuard
    simpa only [d104, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d104, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c441 pattern childGuard
    simpa only [d104, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c443 (pattern : Twelve) (guard : d0 pattern = 1) : d78 pattern ≤ (0 : Int) + d206 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c444 (pattern : Twelve) (guard : d1839 pattern = 1) : d94 pattern ≤ (0 : Int) + d310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d94, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c431 pattern childGuard
    simpa only [d1839, d94, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d94, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c443 pattern childGuard
    simpa only [d1839, d94, d310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c445 (pattern : Twelve) (guard : d1839 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c446 (pattern : Twelve) (guard : d1839 pattern = 1) : d105 pattern ≤ (0 : Int) + d323 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d105, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c444 pattern childGuard
    simpa only [d105, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d105, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d105, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c447 (pattern : Twelve) (guard : d1839 pattern = 1) : d111 pattern ≤ (0 : Int) + d333 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d111, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c442 pattern childGuard
    simpa only [d111, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d111, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c446 pattern childGuard
    simpa only [d111, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c448 (pattern : Twelve) (guard : d1839 pattern = 1) : d114 pattern ≤ (0 : Int) + d338 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d114, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c435 pattern childGuard
    simpa only [d114, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d114, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c447 pattern childGuard
    simpa only [d114, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c449 (pattern : Twelve) (guard : d0 pattern = 1) : d80 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c450 (pattern : Twelve) (guard : d1839 pattern = 1) : d97 pattern ≤ (0 : Int) + d311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d97, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c422 pattern childGuard
    simpa only [d1839, d97, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d97, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c449 pattern childGuard
    simpa only [d1839, d97, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c451 (pattern : Twelve) (guard : d1 pattern = 1) : d83 pattern ≤ (0 : Int) + d83 pattern := by
  omega
theorem c452 (pattern : Twelve) (guard : d0 pattern = 1) : d84 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c453 (pattern : Twelve) (guard : d1839 pattern = 1) : d98 pattern ≤ (0 : Int) + d312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d98, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c451 pattern childGuard
    simpa only [d1839, d98, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d98, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c452 pattern childGuard
    simpa only [d1839, d98, d312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c454 (pattern : Twelve) (guard : d1839 pattern = 1) : d106 pattern ≤ (0 : Int) + d324 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d106, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c450 pattern childGuard
    simpa only [d106, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d106, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c453 pattern childGuard
    simpa only [d106, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c455 (pattern : Twelve) (guard : d1 pattern = 1) : d85 pattern ≤ (0 : Int) + d85 pattern := by
  omega
theorem c456 (pattern : Twelve) (guard : d0 pattern = 1) : d86 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c457 (pattern : Twelve) (guard : d1839 pattern = 1) : d99 pattern ≤ (0 : Int) + d313 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d99, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c455 pattern childGuard
    simpa only [d1839, d99, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d99, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c456 pattern childGuard
    simpa only [d1839, d99, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c458 (pattern : Twelve) (guard : d1839 pattern = 1) : d107 pattern ≤ (0 : Int) + d325 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d107, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c450 pattern childGuard
    simpa only [d107, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d107, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c457 pattern childGuard
    simpa only [d107, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c459 (pattern : Twelve) (guard : d1839 pattern = 1) : d112 pattern ≤ (0 : Int) + d334 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d112, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c454 pattern childGuard
    simpa only [d112, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d112, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c458 pattern childGuard
    simpa only [d112, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c460 (pattern : Twelve) (guard : d1 pattern = 1) : d87 pattern ≤ (0 : Int) + d87 pattern := by
  omega
theorem c461 (pattern : Twelve) (guard : d0 pattern = 1) : d88 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c462 (pattern : Twelve) (guard : d1839 pattern = 1) : d100 pattern ≤ (0 : Int) + d314 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d100, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c460 pattern childGuard
    simpa only [d1839, d100, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d100, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c461 pattern childGuard
    simpa only [d1839, d100, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c463 (pattern : Twelve) (guard : d1 pattern = 1) : d89 pattern ≤ (0 : Int) + d89 pattern := by
  omega
theorem c464 (pattern : Twelve) (guard : d0 pattern = 1) : d90 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c465 (pattern : Twelve) (guard : d1839 pattern = 1) : d101 pattern ≤ (0 : Int) + d315 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d101, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c463 pattern childGuard
    simpa only [d1839, d101, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d101, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c464 pattern childGuard
    simpa only [d1839, d101, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c466 (pattern : Twelve) (guard : d1839 pattern = 1) : d108 pattern ≤ (0 : Int) + d326 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d108, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c462 pattern childGuard
    simpa only [d108, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d108, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c465 pattern childGuard
    simpa only [d108, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c467 (pattern : Twelve) (guard : d1839 pattern = 1) : d109 pattern ≤ (0 : Int) + d327 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d109, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c457 pattern childGuard
    simpa only [d109, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d109, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d109, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c468 (pattern : Twelve) (guard : d1839 pattern = 1) : d113 pattern ≤ (0 : Int) + d335 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d113, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c466 pattern childGuard
    simpa only [d113, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d113, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c467 pattern childGuard
    simpa only [d113, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c469 (pattern : Twelve) (guard : d1839 pattern = 1) : d115 pattern ≤ (0 : Int) + d339 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d115, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c459 pattern childGuard
    simpa only [d115, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d115, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c468 pattern childGuard
    simpa only [d115, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c470 (pattern : Twelve) (guard : d1839 pattern = 1) : d116 pattern ≤ (0 : Int) + d341 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d116, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c448 pattern childGuard
    simpa only [d116, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d116, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c469 pattern childGuard
    simpa only [d116, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c471 (pattern : Twelve) (guard : d0 pattern = 1) : d73 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c472 (pattern : Twelve) (guard : d1839 pattern = 1) : d91 pattern ≤ (0 : Int) + d311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d91, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c422 pattern childGuard
    simpa only [d1839, d91, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d91, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c471 pattern childGuard
    simpa only [d1839, d91, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c473 (pattern : Twelve) (guard : d0 pattern = 1) : d75 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c474 (pattern : Twelve) (guard : d1839 pattern = 1) : d92 pattern ≤ (0 : Int) + d316 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d92, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c425 pattern childGuard
    simpa only [d1839, d92, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d92, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c473 pattern childGuard
    simpa only [d1839, d92, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c475 (pattern : Twelve) (guard : d1839 pattern = 1) : d102 pattern ≤ (0 : Int) + d328 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d102, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c472 pattern childGuard
    simpa only [d102, d328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d102, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c474 pattern childGuard
    simpa only [d102, d328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c476 (pattern : Twelve) (guard : d0 pattern = 1) : d76 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c477 (pattern : Twelve) (guard : d1839 pattern = 1) : d93 pattern ≤ (0 : Int) + d311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d93, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c422 pattern childGuard
    simpa only [d1839, d93, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d93, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c476 pattern childGuard
    simpa only [d1839, d93, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c478 (pattern : Twelve) (guard : d0 pattern = 1) : d78 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c479 (pattern : Twelve) (guard : d1839 pattern = 1) : d94 pattern ≤ (0 : Int) + d317 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d94, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c431 pattern childGuard
    simpa only [d1839, d94, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d94, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c478 pattern childGuard
    simpa only [d1839, d94, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c480 (pattern : Twelve) (guard : d1839 pattern = 1) : d103 pattern ≤ (0 : Int) + d329 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d103, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c477 pattern childGuard
    simpa only [d103, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d103, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c479 pattern childGuard
    simpa only [d103, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c481 (pattern : Twelve) (guard : d1839 pattern = 1) : d110 pattern ≤ (0 : Int) + d336 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d110, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c475 pattern childGuard
    simpa only [d110, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d110, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c480 pattern childGuard
    simpa only [d110, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c482 (pattern : Twelve) (guard : d1839 pattern = 1) : d95 pattern ≤ (0 : Int) + d318 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d95, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c436 pattern childGuard
    simpa only [d1839, d95, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d95, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c449 pattern childGuard
    simpa only [d1839, d95, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c483 (pattern : Twelve) (guard : d0 pattern = 1) : d82 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c484 (pattern : Twelve) (guard : d1839 pattern = 1) : d96 pattern ≤ (0 : Int) + d319 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d96, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c439 pattern childGuard
    simpa only [d1839, d96, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d96, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c483 pattern childGuard
    simpa only [d1839, d96, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c485 (pattern : Twelve) (guard : d1839 pattern = 1) : d104 pattern ≤ (0 : Int) + d330 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d104, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c482 pattern childGuard
    simpa only [d104, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d104, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c484 pattern childGuard
    simpa only [d104, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c486 (pattern : Twelve) (guard : d1839 pattern = 1) : d105 pattern ≤ (0 : Int) + d331 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d105, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c479 pattern childGuard
    simpa only [d105, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d105, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d105, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c487 (pattern : Twelve) (guard : d1839 pattern = 1) : d111 pattern ≤ (0 : Int) + d337 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d111, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c485 pattern childGuard
    simpa only [d111, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d111, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c486 pattern childGuard
    simpa only [d111, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c488 (pattern : Twelve) (guard : d1839 pattern = 1) : d114 pattern ≤ (0 : Int) + d340 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d114, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c481 pattern childGuard
    simpa only [d114, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d114, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c487 pattern childGuard
    simpa only [d114, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c489 (pattern : Twelve) (guard : d1839 pattern = 1) : d116 pattern ≤ (0 : Int) + d342 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d116, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c488 pattern childGuard
    simpa only [d116, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d116, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c469 pattern childGuard
    simpa only [d116, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c490 (pattern : Twelve) (guard : d1839 pattern = 1) : d116 pattern ≤ (0 : Int) + d343 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c470 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c489 pattern childGuard
    simpa only [d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c491 (pattern : Twelve) (guard : d1839 pattern = 1) : d116 pattern ≤ (0 : Int) + d344 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c490 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c489 pattern childGuard
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c492 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (0 : Int) + d838 pattern := by
  omega
theorem c493 (pattern : Twelve) (guard : d0 pattern = 1) : d839 pattern ≤ (0 : Int) + d909 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c494 (pattern : Twelve) (guard : d1839 pattern = 1) : d853 pattern ≤ (0 : Int) + d980 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d853, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c492 pattern childGuard
    simpa only [d1839, d853, d980, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d853, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c493 pattern childGuard
    simpa only [d1839, d853, d980, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c495 (pattern : Twelve) (guard : d1 pattern = 1) : d840 pattern ≤ (0 : Int) + d840 pattern := by
  omega
theorem c496 (pattern : Twelve) (guard : d0 pattern = 1) : d841 pattern ≤ (0 : Int) + d910 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c497 (pattern : Twelve) (guard : d1839 pattern = 1) : d854 pattern ≤ (0 : Int) + d981 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d854, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c495 pattern childGuard
    simpa only [d1839, d854, d981, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d854, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c496 pattern childGuard
    simpa only [d1839, d854, d981, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c498 (pattern : Twelve) (guard : d1839 pattern = 1) : d861 pattern ≤ (0 : Int) + d991 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d861, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c494 pattern childGuard
    simpa only [d861, d991, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d861, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c497 pattern childGuard
    simpa only [d861, d991, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c499 (pattern : Twelve) (guard : d0 pattern = 1) : d839 pattern ≤ (0 : Int) + d910 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c500 (pattern : Twelve) (guard : d1839 pattern = 1) : d853 pattern ≤ (0 : Int) + d982 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d853, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c492 pattern childGuard
    simpa only [d1839, d853, d982, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d853, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c499 pattern childGuard
    simpa only [d1839, d853, d982, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c501 (pattern : Twelve) (guard : d0 pattern = 1) : d841 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c502 (pattern : Twelve) (guard : d1839 pattern = 1) : d854 pattern ≤ (0 : Int) + d983 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d854, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c495 pattern childGuard
    simpa only [d1839, d854, d983, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d854, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c501 pattern childGuard
    simpa only [d1839, d854, d983, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c503 (pattern : Twelve) (guard : d1839 pattern = 1) : d861 pattern ≤ (0 : Int) + d992 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d861, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c500 pattern childGuard
    simpa only [d861, d992, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d861, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c502 pattern childGuard
    simpa only [d861, d992, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c504 (pattern : Twelve) (guard : d1839 pattern = 1) : d861 pattern ≤ (0 : Int) + d1000 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c498 pattern childGuard
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c503 pattern childGuard
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c505 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (0 : Int) + d842 pattern := by
  omega
theorem c506 (pattern : Twelve) (guard : d0 pattern = 1) : d843 pattern ≤ (0 : Int) + d911 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c507 (pattern : Twelve) (guard : d1839 pattern = 1) : d855 pattern ≤ (0 : Int) + d984 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d855, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c505 pattern childGuard
    simpa only [d1839, d855, d984, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d855, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c506 pattern childGuard
    simpa only [d1839, d855, d984, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c508 (pattern : Twelve) (guard : d1 pattern = 1) : d844 pattern ≤ (0 : Int) + d844 pattern := by
  omega
theorem c509 (pattern : Twelve) (guard : d0 pattern = 1) : d845 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c510 (pattern : Twelve) (guard : d1839 pattern = 1) : d856 pattern ≤ (0 : Int) + d985 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d856, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c508 pattern childGuard
    simpa only [d1839, d856, d985, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d856, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c509 pattern childGuard
    simpa only [d1839, d856, d985, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c511 (pattern : Twelve) (guard : d1839 pattern = 1) : d862 pattern ≤ (0 : Int) + d993 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d862, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c507 pattern childGuard
    simpa only [d862, d993, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d862, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c510 pattern childGuard
    simpa only [d862, d993, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c512 (pattern : Twelve) (guard : d1839 pattern = 1) : d863 pattern ≤ (0 : Int) + d994 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d863, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c502 pattern childGuard
    simpa only [d863, d994, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d863, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d863, d994, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c513 (pattern : Twelve) (guard : d1839 pattern = 1) : d867 pattern ≤ (0 : Int) + d1001 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d867, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c511 pattern childGuard
    simpa only [d867, d1001, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d867, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c512 pattern childGuard
    simpa only [d867, d1001, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c514 (pattern : Twelve) (guard : d1839 pattern = 1) : d869 pattern ≤ (0 : Int) + d1004 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d869, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c504 pattern childGuard
    simpa only [d869, d1004, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d869, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c513 pattern childGuard
    simpa only [d869, d1004, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c515 (pattern : Twelve) (guard : d0 pattern = 1) : d846 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c516 (pattern : Twelve) (guard : d1839 pattern = 1) : d857 pattern ≤ (0 : Int) + d986 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d857, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c492 pattern childGuard
    simpa only [d1839, d857, d986, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d857, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c515 pattern childGuard
    simpa only [d1839, d857, d986, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c517 (pattern : Twelve) (guard : d1 pattern = 1) : d847 pattern ≤ (0 : Int) + d847 pattern := by
  omega
theorem c518 (pattern : Twelve) (guard : d0 pattern = 1) : d848 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c519 (pattern : Twelve) (guard : d1839 pattern = 1) : d858 pattern ≤ (0 : Int) + d987 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d858, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c517 pattern childGuard
    simpa only [d1839, d858, d987, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d858, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c518 pattern childGuard
    simpa only [d1839, d858, d987, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c520 (pattern : Twelve) (guard : d1839 pattern = 1) : d864 pattern ≤ (0 : Int) + d995 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d864, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c516 pattern childGuard
    simpa only [d864, d995, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d864, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c519 pattern childGuard
    simpa only [d864, d995, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c521 (pattern : Twelve) (guard : d1 pattern = 1) : d849 pattern ≤ (0 : Int) + d849 pattern := by
  omega
theorem c522 (pattern : Twelve) (guard : d0 pattern = 1) : d850 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c523 (pattern : Twelve) (guard : d1839 pattern = 1) : d859 pattern ≤ (0 : Int) + d988 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d859, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c521 pattern childGuard
    simpa only [d1839, d859, d988, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d859, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c522 pattern childGuard
    simpa only [d1839, d859, d988, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c524 (pattern : Twelve) (guard : d1 pattern = 1) : d851 pattern ≤ (0 : Int) + d851 pattern := by
  omega
theorem c525 (pattern : Twelve) (guard : d0 pattern = 1) : d852 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c526 (pattern : Twelve) (guard : d1839 pattern = 1) : d860 pattern ≤ (0 : Int) + d989 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d860, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d1839, d860, d989, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d860, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c525 pattern childGuard
    simpa only [d1839, d860, d989, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c527 (pattern : Twelve) (guard : d1839 pattern = 1) : d865 pattern ≤ (0 : Int) + d996 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d865, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c523 pattern childGuard
    simpa only [d865, d996, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d865, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c526 pattern childGuard
    simpa only [d865, d996, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c528 (pattern : Twelve) (guard : d1839 pattern = 1) : d866 pattern ≤ (0 : Int) + d997 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d866, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c519 pattern childGuard
    simpa only [d866, d997, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d866, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d866, d997, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c529 (pattern : Twelve) (guard : d1839 pattern = 1) : d868 pattern ≤ (0 : Int) + d1002 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d868, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c527 pattern childGuard
    simpa only [d868, d1002, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d868, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c528 pattern childGuard
    simpa only [d868, d1002, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c530 (pattern : Twelve) (guard : d1839 pattern = 1) : d870 pattern ≤ (0 : Int) + d1005 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d870, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c520 pattern childGuard
    simpa only [d870, d1005, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d870, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c529 pattern childGuard
    simpa only [d870, d1005, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c531 (pattern : Twelve) (guard : d1839 pattern = 1) : d871 pattern ≤ (0 : Int) + d1007 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d871, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c514 pattern childGuard
    simpa only [d871, d1007, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d871, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c530 pattern childGuard
    simpa only [d871, d1007, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c532 (pattern : Twelve) (guard : d0 pattern = 1) : d839 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c533 (pattern : Twelve) (guard : d1839 pattern = 1) : d853 pattern ≤ (0 : Int) + d986 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d853, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c492 pattern childGuard
    simpa only [d1839, d853, d986, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d853, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c532 pattern childGuard
    simpa only [d1839, d853, d986, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c534 (pattern : Twelve) (guard : d1839 pattern = 1) : d861 pattern ≤ (0 : Int) + d998 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d861, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c533 pattern childGuard
    simpa only [d861, d998, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d861, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c502 pattern childGuard
    simpa only [d861, d998, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c535 (pattern : Twelve) (guard : d0 pattern = 1) : d843 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c536 (pattern : Twelve) (guard : d1839 pattern = 1) : d855 pattern ≤ (0 : Int) + d990 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d855, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c505 pattern childGuard
    simpa only [d1839, d855, d990, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d855, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c535 pattern childGuard
    simpa only [d1839, d855, d990, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c537 (pattern : Twelve) (guard : d1839 pattern = 1) : d862 pattern ≤ (0 : Int) + d999 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d862, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c536 pattern childGuard
    simpa only [d862, d999, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d862, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c510 pattern childGuard
    simpa only [d862, d999, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c538 (pattern : Twelve) (guard : d1839 pattern = 1) : d867 pattern ≤ (0 : Int) + d1003 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d867, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c537 pattern childGuard
    simpa only [d867, d1003, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d867, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c512 pattern childGuard
    simpa only [d867, d1003, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c539 (pattern : Twelve) (guard : d1839 pattern = 1) : d869 pattern ≤ (0 : Int) + d1006 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d869, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c534 pattern childGuard
    simpa only [d869, d1006, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d869, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c538 pattern childGuard
    simpa only [d869, d1006, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c540 (pattern : Twelve) (guard : d1839 pattern = 1) : d871 pattern ≤ (0 : Int) + d1008 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d871, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c539 pattern childGuard
    simpa only [d871, d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d871, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c530 pattern childGuard
    simpa only [d871, d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c541 (pattern : Twelve) (guard : d1839 pattern = 1) : d871 pattern ≤ (0 : Int) + d1009 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c531 pattern childGuard
    simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c540 pattern childGuard
    simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c542 (pattern : Twelve) (guard : d1839 pattern = 1) : d871 pattern ≤ (0 : Int) + d1010 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c541 pattern childGuard
    simpa only [d1010, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c540 pattern childGuard
    simpa only [d1010, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c543 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1293 pattern := by
  omega
theorem c544 (pattern : Twelve) (guard : d0 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1355 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c545 (pattern : Twelve) (guard : d1839 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1412 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1305, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c543 pattern childGuard
    simpa only [d1839, d1305, d1412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1305, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c544 pattern childGuard
    simpa only [d1839, d1305, d1412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c546 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (0 : Int) + d1295 pattern := by
  omega
theorem c547 (pattern : Twelve) (guard : d0 pattern = 1) : d1296 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c548 (pattern : Twelve) (guard : d1839 pattern = 1) : d1306 pattern ≤ (0 : Int) + d1413 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1306, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c546 pattern childGuard
    simpa only [d1839, d1306, d1413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1306, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c547 pattern childGuard
    simpa only [d1839, d1306, d1413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c549 (pattern : Twelve) (guard : d1839 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1417 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1313, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c545 pattern childGuard
    simpa only [d1313, d1417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1313, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c548 pattern childGuard
    simpa only [d1313, d1417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c550 (pattern : Twelve) (guard : d0 pattern = 1) : d1294 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c551 (pattern : Twelve) (guard : d1839 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1414 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1305, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c543 pattern childGuard
    simpa only [d1839, d1305, d1414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1305, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c550 pattern childGuard
    simpa only [d1839, d1305, d1414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c552 (pattern : Twelve) (guard : d1839 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1313, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c551 pattern childGuard
    simpa only [d1313, d1418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1313, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c548 pattern childGuard
    simpa only [d1313, d1418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c553 (pattern : Twelve) (guard : d1839 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1421 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c549 pattern childGuard
    simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c552 pattern childGuard
    simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c554 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (0 : Int) + d1297 pattern := by
  omega
theorem c555 (pattern : Twelve) (guard : d0 pattern = 1) : d1298 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c556 (pattern : Twelve) (guard : d1839 pattern = 1) : d1307 pattern ≤ (0 : Int) + d1415 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1307, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c554 pattern childGuard
    simpa only [d1839, d1307, d1415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1307, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c555 pattern childGuard
    simpa only [d1839, d1307, d1415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c557 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (0 : Int) + d1299 pattern := by
  omega
theorem c558 (pattern : Twelve) (guard : d0 pattern = 1) : d1300 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c559 (pattern : Twelve) (guard : d1839 pattern = 1) : d1308 pattern ≤ (0 : Int) + d1416 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1308, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c557 pattern childGuard
    simpa only [d1839, d1308, d1416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1308, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c558 pattern childGuard
    simpa only [d1839, d1308, d1416, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
