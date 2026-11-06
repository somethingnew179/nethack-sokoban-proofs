/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare420 (p : Pattern) (guard : d741 p = 1) : d150 p ≤ (2 : Int) + d780 p := by
  cases selected : p 141 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d150, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare414 p hg
    simpa only [d150, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d150, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare419 p hg
    simpa only [d150, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare421 (p : Pattern) (guard : d741 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  omega
theorem compare422 (p : Pattern) (guard : d741 p = 1) : d151 p ≤ (2 : Int) + d781 p := by
  cases selected : p 134 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d151, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare420 p hg
    simpa only [d151, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d151, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare421 p hg
    simpa only [d151, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare423 (p : Pattern) (guard : d741 p = 1) : d152 p ≤ (2 : Int) + d782 p := by
  cases selected : p 133 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d152, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare409 p hg
    simpa only [d152, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d152, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare422 p hg
    simpa only [d152, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare424 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (2 : Int) + d785 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare425 (p : Pattern) (guard : d774 p = 1) : d200 p ≤ (2 : Int) + d786 p := by
  cases selected : p 132 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d774, d200, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare423 p hg
    simpa only [d774, d200, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d200, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare424 p hg
    simpa only [d774, d200, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare426 (p : Pattern) (guard : d774 p = 1) : d201 p ≤ (2 : Int) + d787 p := by
  cases selected : p 108 with
  | false =>
    have hg : d774 p = 1 := by simpa only [d201, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare408 p hg
    simpa only [d201, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d201, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare425 p hg
    simpa only [d201, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare427 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d215 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare428 (p : Pattern) (guard : d754 p = 1) : d199 p ≤ (0 : Int) + d216 p := by
  cases selected : p 132 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d199, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare154 p hg
    simpa only [d754, d199, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d199, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare427 p hg
    simpa only [d754, d199, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare429 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d73 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare430 (p : Pattern) (guard : d754 p = 1) : d200 p ≤ (0 : Int) + d218 p := by
  cases selected : p 132 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d200, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare159 p hg
    simpa only [d754, d200, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d200, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare429 p hg
    simpa only [d754, d200, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare431 (p : Pattern) (guard : d754 p = 1) : d201 p ≤ (0 : Int) + d219 p := by
  cases selected : p 108 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d201, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare428 p hg
    simpa only [d201, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d201, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare430 p hg
    simpa only [d201, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare432 (p : Pattern) (guard : d0 p = 1) : d113 p ≤ (0 : Int) + d112 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare433 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (0 : Int) + d55 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare434 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare433 p hg
    simpa only [d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare435 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (0 : Int) + d107 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d114, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare434 p hg
    simpa only [d114, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d114, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d114, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare436 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (0 : Int) + d108 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare434 p hg
    simpa only [d115, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare435 p hg
    simpa only [d115, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare437 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (0 : Int) + d60 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare301 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare303 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare438 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (0 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare433 p hg
    simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare437 p hg
    simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare439 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare294 p hg
    simpa only [d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare438 p hg
    simpa only [d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare440 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare441 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (0 : Int) + d110 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare439 p hg
    simpa only [d116, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare440 p hg
    simpa only [d116, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare442 (p : Pattern) (guard : d1 p = 1) : d117 p ≤ (0 : Int) + d111 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d117, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare439 p hg
    simpa only [d117, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d117, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare441 p hg
    simpa only [d117, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare443 (p : Pattern) (guard : d1 p = 1) : d118 p ≤ (0 : Int) + d112 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d118, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare436 p hg
    simpa only [d118, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d118, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare442 p hg
    simpa only [d118, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare444 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (0 : Int) + d112 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare445 (p : Pattern) (guard : d737 p = 1) : d133 p ≤ (0 : Int) + d112 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d737, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare443 p hg
    simpa only [d737, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d737, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare444 p hg
    simpa only [d737, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare446 (p : Pattern) (guard : d789 p = 1) : d134 p ≤ (0 : Int) + d112 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d789, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare432 p hg
    simpa only [d789, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d737 p = 1 := by simpa only [d789, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare445 p hg
    simpa only [d789, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare447 (p : Pattern) (guard : d790 p = 1) : d199 p ≤ (0 : Int) + d791 p := by
  cases selected : p 132 with
  | false =>
    have hg : d789 p = 1 := by simpa only [d790, d199, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare446 p hg
    simpa only [d790, d199, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d790, d199, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d790, d199, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare448 (p : Pattern) (guard : d0 p = 1) : d67 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare449 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (0 : Int) + d55 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare450 (p : Pattern) (guard : d1 p = 1) : d137 p ≤ (0 : Int) + d55 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare449 p hg
    simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare451 (p : Pattern) (guard : d1 p = 1) : d138 p ≤ (0 : Int) + d55 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare450 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare452 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (0 : Int) + d55 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare449 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare453 (p : Pattern) (guard : d1 p = 1) : d139 p ≤ (0 : Int) + d55 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare452 p hg
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare450 p hg
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare454 (p : Pattern) (guard : d1 p = 1) : d140 p ≤ (0 : Int) + d55 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare451 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare453 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare455 (p : Pattern) (guard : d1 p = 1) : d141 p ≤ (0 : Int) + d55 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare453 p hg
    simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare456 (p : Pattern) (guard : d1 p = 1) : d142 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare454 p hg
    simpa only [d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare455 p hg
    simpa only [d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare457 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (0 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d12, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d12, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d12, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare301 p hg
    simpa only [d12, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare458 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (0 : Int) + d60 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare301 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare303 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare459 (p : Pattern) (guard : d1 p = 1) : d143 p ≤ (0 : Int) + d60 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare458 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare303 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare460 (p : Pattern) (guard : d1 p = 1) : d144 p ≤ (0 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare450 p hg
    simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare459 p hg
    simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare461 (p : Pattern) (guard : d1 p = 1) : d145 p ≤ (0 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare457 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare460 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare462 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (0 : Int) + d60 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare301 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare458 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare463 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (0 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare452 p hg
    simpa only [d127, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare462 p hg
    simpa only [d127, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare464 (p : Pattern) (guard : d1 p = 1) : d146 p ≤ (0 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare463 p hg
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare460 p hg
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare465 (p : Pattern) (guard : d1 p = 1) : d147 p ≤ (0 : Int) + d65 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare461 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare464 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare466 (p : Pattern) (guard : d1 p = 1) : d148 p ≤ (0 : Int) + d65 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare464 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare440 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare467 (p : Pattern) (guard : d1 p = 1) : d149 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare465 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare466 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare468 (p : Pattern) (guard : d1 p = 1) : d150 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d150, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare456 p hg
    simpa only [d150, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d150, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare467 p hg
    simpa only [d150, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare469 (p : Pattern) (guard : d737 p = 1) : d151 p ≤ (0 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d737, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare468 p hg
    simpa only [d737, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d737, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d737, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare470 (p : Pattern) (guard : d789 p = 1) : d152 p ≤ (0 : Int) + d66 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d789, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare448 p hg
    simpa only [d789, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d737 p = 1 := by simpa only [d789, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare469 p hg
    simpa only [d789, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare471 (p : Pattern) (guard : d790 p = 1) : d200 p ≤ (0 : Int) + d66 p := by
  cases selected : p 132 with
  | false =>
    have hg : d789 p = 1 := by simpa only [d790, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare470 p hg
    simpa only [d790, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d790, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d790, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare472 (p : Pattern) (guard : d790 p = 1) : d201 p ≤ (0 : Int) + d792 p := by
  cases selected : p 108 with
  | false =>
    have hg : d790 p = 1 := by simpa only [d201, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare447 p hg
    simpa only [d201, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d790 p = 1 := by simpa only [d201, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare471 p hg
    simpa only [d201, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare473 (p : Pattern) (guard : d794 p = 1) : d57 p ≤ (0 : Int) + d114 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare318 p hg
    simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare474 (p : Pattern) (guard : d794 p = 1) : d63 p ≤ (0 : Int) + d116 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare321 p hg
    simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare475 (p : Pattern) (guard : d794 p = 1) : d64 p ≤ (0 : Int) + d335 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d64, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare473 p hg
    simpa only [d64, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d64, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare474 p hg
    simpa only [d64, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare476 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare477 (p : Pattern) (guard : d794 p = 1) : d106 p ≤ (0 : Int) + d107 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare324 p hg
    simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare476 p hg
    simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare478 (p : Pattern) (guard : d794 p = 1) : d107 p ≤ (0 : Int) + d107 p := by
  omega
theorem compare479 (p : Pattern) (guard : d794 p = 1) : d108 p ≤ (0 : Int) + d107 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare477 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare478 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare480 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare481 (p : Pattern) (guard : d794 p = 1) : d109 p ≤ (0 : Int) + d110 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare327 p hg
    simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare480 p hg
    simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare482 (p : Pattern) (guard : d794 p = 1) : d110 p ≤ (0 : Int) + d110 p := by
  omega
theorem compare483 (p : Pattern) (guard : d794 p = 1) : d111 p ≤ (0 : Int) + d110 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare481 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare482 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare484 (p : Pattern) (guard : d794 p = 1) : d112 p ≤ (0 : Int) + d336 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d112, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare479 p hg
    simpa only [d112, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d112, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare483 p hg
    simpa only [d112, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare485 (p : Pattern) (guard : d794 p = 1) : d113 p ≤ (0 : Int) + d337 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d113, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare475 p hg
    simpa only [d113, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d113, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare484 p hg
    simpa only [d113, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare486 (p : Pattern) (guard : d798 p = 1) : d115 p ≤ (0 : Int) + d338 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d115, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare473 p hg
    simpa only [d798, d115, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d115, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare332 p hg
    simpa only [d798, d115, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare487 (p : Pattern) (guard : d798 p = 1) : d117 p ≤ (0 : Int) + d339 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d117, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare474 p hg
    simpa only [d798, d117, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d117, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare334 p hg
    simpa only [d798, d117, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare488 (p : Pattern) (guard : d798 p = 1) : d118 p ≤ (0 : Int) + d340 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d118, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare486 p hg
    simpa only [d118, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d118, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare487 p hg
    simpa only [d118, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare489 (p : Pattern) (guard : d0 p = 1) : d121 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare490 (p : Pattern) (guard : d794 p = 1) : d122 p ≤ (0 : Int) + d107 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d122, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare324 p hg
    simpa only [d794, d122, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d122, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare489 p hg
    simpa only [d794, d122, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare491 (p : Pattern) (guard : d798 p = 1) : d124 p ≤ (0 : Int) + d211 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d124, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare490 p hg
    simpa only [d798, d124, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d124, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare338 p hg
    simpa only [d798, d124, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare492 (p : Pattern) (guard : d0 p = 1) : d128 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare493 (p : Pattern) (guard : d794 p = 1) : d129 p ≤ (0 : Int) + d110 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d129, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare327 p hg
    simpa only [d794, d129, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d129, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare492 p hg
    simpa only [d794, d129, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare494 (p : Pattern) (guard : d798 p = 1) : d131 p ≤ (0 : Int) + d212 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d131, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare493 p hg
    simpa only [d798, d131, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d131, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare341 p hg
    simpa only [d798, d131, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare495 (p : Pattern) (guard : d798 p = 1) : d132 p ≤ (0 : Int) + d213 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d132, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare491 p hg
    simpa only [d132, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d132, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare494 p hg
    simpa only [d132, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare496 (p : Pattern) (guard : d798 p = 1) : d133 p ≤ (0 : Int) + d341 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d133, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare488 p hg
    simpa only [d133, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d133, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare495 p hg
    simpa only [d133, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare497 (p : Pattern) (guard : d799 p = 1) : d134 p ≤ (0 : Int) + d342 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d799, d134, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare485 p hg
    simpa only [d799, d134, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d799, d134, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare496 p hg
    simpa only [d799, d134, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare498 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d343 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare499 (p : Pattern) (guard : d800 p = 1) : d199 p ≤ (0 : Int) + d344 p := by
  cases selected : p 132 with
  | false =>
    have hg : d799 p = 1 := by simpa only [d800, d199, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare497 p hg
    simpa only [d800, d199, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d800, d199, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare498 p hg
    simpa only [d800, d199, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare500 (p : Pattern) (guard : d794 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare501 (p : Pattern) (guard : d794 p = 1) : d67 p ≤ (0 : Int) + d345 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d67, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare475 p hg
    simpa only [d67, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d67, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d67, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare502 (p : Pattern) (guard : d1 p = 1) : d138 p ≤ (0 : Int) + d138 p := by
  omega
theorem compare503 (p : Pattern) (guard : d0 p = 1) : d139 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare504 (p : Pattern) (guard : d794 p = 1) : d140 p ≤ (0 : Int) + d346 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d140, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare502 p hg
    simpa only [d794, d140, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d140, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare503 p hg
    simpa only [d794, d140, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare505 (p : Pattern) (guard : d798 p = 1) : d142 p ≤ (0 : Int) + d347 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d142, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare504 p hg
    simpa only [d798, d142, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d142, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare351 p hg
    simpa only [d798, d142, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare506 (p : Pattern) (guard : d1 p = 1) : d145 p ≤ (0 : Int) + d145 p := by
  omega
theorem compare507 (p : Pattern) (guard : d0 p = 1) : d146 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare508 (p : Pattern) (guard : d794 p = 1) : d147 p ≤ (0 : Int) + d348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d147, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare506 p hg
    simpa only [d794, d147, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d147, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare507 p hg
    simpa only [d794, d147, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare509 (p : Pattern) (guard : d798 p = 1) : d149 p ≤ (0 : Int) + d349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d149, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare508 p hg
    simpa only [d798, d149, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d149, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare354 p hg
    simpa only [d798, d149, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare510 (p : Pattern) (guard : d798 p = 1) : d150 p ≤ (0 : Int) + d350 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d150, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare505 p hg
    simpa only [d150, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d150, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare509 p hg
    simpa only [d150, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare511 (p : Pattern) (guard : d798 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare512 (p : Pattern) (guard : d798 p = 1) : d151 p ≤ (0 : Int) + d351 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d151, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare510 p hg
    simpa only [d151, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d151, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d151, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare513 (p : Pattern) (guard : d799 p = 1) : d152 p ≤ (0 : Int) + d352 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d799, d152, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare501 p hg
    simpa only [d799, d152, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d799, d152, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare512 p hg
    simpa only [d799, d152, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare514 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d354 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare515 (p : Pattern) (guard : d800 p = 1) : d200 p ≤ (0 : Int) + d355 p := by
  cases selected : p 132 with
  | false =>
    have hg : d799 p = 1 := by simpa only [d800, d200, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare513 p hg
    simpa only [d800, d200, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d800, d200, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare514 p hg
    simpa only [d800, d200, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare516 (p : Pattern) (guard : d800 p = 1) : d201 p ≤ (0 : Int) + d356 p := by
  cases selected : p 108 with
  | false =>
    have hg : d800 p = 1 := by simpa only [d201, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare499 p hg
    simpa only [d201, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d800 p = 1 := by simpa only [d201, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare515 p hg
    simpa only [d201, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare517 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d341 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare518 (p : Pattern) (guard : d801 p = 1) : d210 p ≤ (0 : Int) + d342 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d801, d210, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare485 p hg
    simpa only [d801, d210, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d801, d210, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare517 p hg
    simpa only [d801, d210, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare519 (p : Pattern) (guard : d794 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare520 (p : Pattern) (guard : d794 p = 1) : d68 p ≤ (0 : Int) + d338 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d68, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare473 p hg
    simpa only [d68, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d68, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare519 p hg
    simpa only [d68, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare521 (p : Pattern) (guard : d794 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare522 (p : Pattern) (guard : d794 p = 1) : d69 p ≤ (0 : Int) + d339 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d69, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare474 p hg
    simpa only [d69, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d69, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare521 p hg
    simpa only [d69, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare523 (p : Pattern) (guard : d794 p = 1) : d70 p ≤ (0 : Int) + d340 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d70, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare520 p hg
    simpa only [d70, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d70, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare522 p hg
    simpa only [d70, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare524 (p : Pattern) (guard : d794 p = 1) : d213 p ≤ (0 : Int) + d213 p := by
  omega
theorem compare525 (p : Pattern) (guard : d794 p = 1) : d214 p ≤ (0 : Int) + d341 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d214, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare523 p hg
    simpa only [d214, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d214, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare524 p hg
    simpa only [d214, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare526 (p : Pattern) (guard : d801 p = 1) : d215 p ≤ (0 : Int) + d343 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d801, d215, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare525 p hg
    simpa only [d801, d215, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d801, d215, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d801, d215, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare527 (p : Pattern) (guard : d801 p = 1) : d216 p ≤ (0 : Int) + d344 p := by
  cases selected : p 132 with
  | false =>
    have hg : d801 p = 1 := by simpa only [d216, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare518 p hg
    simpa only [d216, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d801 p = 1 := by simpa only [d216, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare526 p hg
    simpa only [d216, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare528 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d351 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare529 (p : Pattern) (guard : d801 p = 1) : d217 p ≤ (0 : Int) + d352 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d801, d217, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare501 p hg
    simpa only [d801, d217, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d801, d217, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare528 p hg
    simpa only [d801, d217, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare530 (p : Pattern) (guard : d794 p = 1) : d71 p ≤ (0 : Int) + d353 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d71, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare523 p hg
    simpa only [d71, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d71, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d71, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare531 (p : Pattern) (guard : d801 p = 1) : d73 p ≤ (0 : Int) + d354 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d801, d73, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare530 p hg
    simpa only [d801, d73, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d801, d73, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d801, d73, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare532 (p : Pattern) (guard : d801 p = 1) : d218 p ≤ (0 : Int) + d355 p := by
  cases selected : p 132 with
  | false =>
    have hg : d801 p = 1 := by simpa only [d218, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare529 p hg
    simpa only [d218, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d801 p = 1 := by simpa only [d218, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare531 p hg
    simpa only [d218, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare533 (p : Pattern) (guard : d801 p = 1) : d219 p ≤ (0 : Int) + d356 p := by
  cases selected : p 108 with
  | false =>
    have hg : d801 p = 1 := by simpa only [d219, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare527 p hg
    simpa only [d219, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d801 p = 1 := by simpa only [d219, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare532 p hg
    simpa only [d219, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare534 (p : Pattern) (guard : d793 p = 1) : d64 p ≤ (2 : Int) + d64 p := by
  omega
theorem compare535 (p : Pattern) (guard : d793 p = 1) : d106 p ≤ (2 : Int) + d106 p := by
  omega
theorem compare536 (p : Pattern) (guard : d793 p = 1) : d107 p ≤ (2 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d793, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare379 p hg
    simpa only [d793, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d793, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare380 p hg
    simpa only [d793, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare537 (p : Pattern) (guard : d793 p = 1) : d108 p ≤ (2 : Int) + d106 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare535 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare538 (p : Pattern) (guard : d793 p = 1) : d109 p ≤ (2 : Int) + d109 p := by
  omega
theorem compare539 (p : Pattern) (guard : d793 p = 1) : d110 p ≤ (2 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d793, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare383 p hg
    simpa only [d793, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d793, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare384 p hg
    simpa only [d793, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare540 (p : Pattern) (guard : d793 p = 1) : d111 p ≤ (2 : Int) + d109 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare538 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare539 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare541 (p : Pattern) (guard : d793 p = 1) : d112 p ≤ (2 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare537 p hg
    simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare540 p hg
    simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare542 (p : Pattern) (guard : d793 p = 1) : d113 p ≤ (2 : Int) + d228 p := by
  cases selected : p 134 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d113, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare534 p hg
    simpa only [d113, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d113, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare541 p hg
    simpa only [d113, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare543 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (2 : Int) + d232 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare544 (p : Pattern) (guard : d802 p = 1) : d210 p ≤ (2 : Int) + d233 p := by
  cases selected : p 133 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d802, d210, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare542 p hg
    simpa only [d802, d210, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d802, d210, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare543 p hg
    simpa only [d802, d210, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare545 (p : Pattern) (guard : d793 p = 1) : d70 p ≤ (2 : Int) + d70 p := by
  omega
theorem compare546 (p : Pattern) (guard : d793 p = 1) : d55 p ≤ (2 : Int) + d55 p := by
  omega
theorem compare547 (p : Pattern) (guard : d793 p = 1) : d211 p ≤ (2 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d211, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d211, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d211, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare546 p hg
    simpa only [d211, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare548 (p : Pattern) (guard : d793 p = 1) : d65 p ≤ (2 : Int) + d65 p := by
  omega
theorem compare549 (p : Pattern) (guard : d793 p = 1) : d212 p ≤ (2 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d212, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare539 p hg
    simpa only [d212, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d212, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare548 p hg
    simpa only [d212, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare550 (p : Pattern) (guard : d793 p = 1) : d213 p ≤ (2 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d213, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare547 p hg
    simpa only [d213, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d213, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare549 p hg
    simpa only [d213, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare551 (p : Pattern) (guard : d793 p = 1) : d214 p ≤ (2 : Int) + d232 p := by
  cases selected : p 134 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d214, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare545 p hg
    simpa only [d214, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d214, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare550 p hg
    simpa only [d214, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare552 (p : Pattern) (guard : d802 p = 1) : d215 p ≤ (2 : Int) + d234 p := by
  cases selected : p 133 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d802, d215, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare551 p hg
    simpa only [d802, d215, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d802, d215, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d802, d215, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare553 (p : Pattern) (guard : d802 p = 1) : d216 p ≤ (2 : Int) + d235 p := by
  cases selected : p 132 with
  | false =>
    have hg : d802 p = 1 := by simpa only [d216, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare544 p hg
    simpa only [d216, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d802 p = 1 := by simpa only [d216, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare552 p hg
    simpa only [d216, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare554 (p : Pattern) (guard : d793 p = 1) : d67 p ≤ (2 : Int) + d67 p := by
  omega
theorem compare555 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (2 : Int) + d806 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare556 (p : Pattern) (guard : d802 p = 1) : d217 p ≤ (2 : Int) + d807 p := by
  cases selected : p 133 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d802, d217, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare554 p hg
    simpa only [d802, d217, d807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d802, d217, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare555 p hg
    simpa only [d802, d217, d807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare557 (p : Pattern) (guard : d802 p = 1) : d73 p ≤ (2 : Int) + d73 p := by
  omega
theorem compare558 (p : Pattern) (guard : d802 p = 1) : d218 p ≤ (2 : Int) + d808 p := by
  cases selected : p 132 with
  | false =>
    have hg : d802 p = 1 := by simpa only [d218, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare556 p hg
    simpa only [d218, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d802 p = 1 := by simpa only [d218, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare557 p hg
    simpa only [d218, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare559 (p : Pattern) (guard : d802 p = 1) : d219 p ≤ (2 : Int) + d809 p := by
  cases selected : p 108 with
  | false =>
    have hg : d802 p = 1 := by simpa only [d219, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare553 p hg
    simpa only [d219, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d802 p = 1 := by simpa only [d219, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare558 p hg
    simpa only [d219, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
