/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons038
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5460 (p : Pattern) (guard : d1092 p = 1) : d443 p ≤ (0 : Int) + d520 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d443, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5459 p hg
    simpa only [d443, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d443, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5413 p hg
    simpa only [d443, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5461 (p : Pattern) (guard : d1092 p = 1) : d444 p ≤ (0 : Int) + d529 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d444, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5433 p hg
    simpa only [d444, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d444, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5460 p hg
    simpa only [d444, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5462 (p : Pattern) (guard : d1092 p = 1) : d445 p ≤ (0 : Int) + d530 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d445, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5415 p hg
    simpa only [d445, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d445, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5461 p hg
    simpa only [d445, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5463 (p : Pattern) (guard : d1092 p = 1) : d446 p ≤ (0 : Int) + d125 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d446, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5440 p hg
    simpa only [d446, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d446, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d446, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5464 (p : Pattern) (guard : d1092 p = 1) : d447 p ≤ (0 : Int) + d126 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d447, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5441 p hg
    simpa only [d447, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d447, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5463 p hg
    simpa only [d447, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5465 (p : Pattern) (guard : d1092 p = 1) : d448 p ≤ (0 : Int) + d531 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d448, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5428 p hg
    simpa only [d448, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d448, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5464 p hg
    simpa only [d448, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5466 (p : Pattern) (guard : d1092 p = 1) : d449 p ≤ (0 : Int) + d532 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d449, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5462 p hg
    simpa only [d449, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d449, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5465 p hg
    simpa only [d449, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5467 (p : Pattern) (guard : d1092 p = 1) : d450 p ≤ (0 : Int) + d533 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d450, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5435 p hg
    simpa only [d450, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d450, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5454 p hg
    simpa only [d450, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5468 (p : Pattern) (guard : d1092 p = 1) : d451 p ≤ (0 : Int) + d130 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d451, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5443 p hg
    simpa only [d451, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d451, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2105 p hg
    simpa only [d451, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5469 (p : Pattern) (guard : d1092 p = 1) : d452 p ≤ (0 : Int) + d534 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d452, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5467 p hg
    simpa only [d452, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d452, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5468 p hg
    simpa only [d452, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5470 (p : Pattern) (guard : d1092 p = 1) : d453 p ≤ (0 : Int) + d535 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d453, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5466 p hg
    simpa only [d453, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d453, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5469 p hg
    simpa only [d453, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5471 (p : Pattern) (guard : d1092 p = 1) : d454 p ≤ (0 : Int) + d536 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d454, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5457 p hg
    simpa only [d454, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d454, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5470 p hg
    simpa only [d454, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5472 (p : Pattern) (guard : d1092 p = 1) : d455 p ≤ (0 : Int) + d537 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d455, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5447 p hg
    simpa only [d455, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d455, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5471 p hg
    simpa only [d455, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5473 (p : Pattern) (guard : d857 p = 1) : d399 p ≤ (0 : Int) + d15 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d857, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3066 p hg
    simpa only [d857, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5474 (p : Pattern) (guard : d857 p = 1) : d400 p ≤ (0 : Int) + d25 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare217 p hg
    simpa only [d857, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3654 p hg
    simpa only [d857, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5475 (p : Pattern) (guard : d857 p = 1) : d401 p ≤ (0 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d401, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5473 p hg
    simpa only [d401, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d401, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5474 p hg
    simpa only [d401, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5476 (p : Pattern) (guard : d857 p = 1) : d402 p ≤ (0 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d402, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5473 p hg
    simpa only [d402, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d402, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5475 p hg
    simpa only [d402, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5477 (p : Pattern) (guard : d857 p = 1) : d403 p ≤ (0 : Int) + d34 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare229 p hg
    simpa only [d857, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3657 p hg
    simpa only [d857, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5478 (p : Pattern) (guard : d857 p = 1) : d404 p ≤ (0 : Int) + d48 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d404, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5473 p hg
    simpa only [d404, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d404, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5477 p hg
    simpa only [d404, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5479 (p : Pattern) (guard : d857 p = 1) : d405 p ≤ (0 : Int) + d41 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare236 p hg
    simpa only [d857, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3068 p hg
    simpa only [d857, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5480 (p : Pattern) (guard : d857 p = 1) : d406 p ≤ (0 : Int) + d49 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d406, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5479 p hg
    simpa only [d406, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d406, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5474 p hg
    simpa only [d406, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5481 (p : Pattern) (guard : d857 p = 1) : d407 p ≤ (0 : Int) + d50 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d407, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5478 p hg
    simpa only [d407, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d407, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5480 p hg
    simpa only [d407, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5482 (p : Pattern) (guard : d857 p = 1) : d408 p ≤ (0 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d408, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5476 p hg
    simpa only [d408, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d408, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5481 p hg
    simpa only [d408, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5483 (p : Pattern) (guard : d857 p = 1) : d399 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d399, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d857, d399, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d399, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5362 p hg
    simpa only [d857, d399, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5484 (p : Pattern) (guard : d857 p = 1) : d400 p ≤ (0 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d400, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare217 p hg
    simpa only [d857, d400, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d400, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5367 p hg
    simpa only [d857, d400, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5485 (p : Pattern) (guard : d857 p = 1) : d401 p ≤ (0 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d401, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5483 p hg
    simpa only [d401, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d401, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5484 p hg
    simpa only [d401, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5486 (p : Pattern) (guard : d857 p = 1) : d402 p ≤ (0 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d402, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5483 p hg
    simpa only [d402, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d402, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5485 p hg
    simpa only [d402, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5487 (p : Pattern) (guard : d857 p = 1) : d403 p ≤ (0 : Int) + d59 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d403, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare229 p hg
    simpa only [d857, d403, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d403, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5371 p hg
    simpa only [d857, d403, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5488 (p : Pattern) (guard : d857 p = 1) : d404 p ≤ (0 : Int) + d60 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d404, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5483 p hg
    simpa only [d404, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d404, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5487 p hg
    simpa only [d404, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5489 (p : Pattern) (guard : d857 p = 1) : d405 p ≤ (0 : Int) + d62 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d405, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare236 p hg
    simpa only [d857, d405, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d405, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5374 p hg
    simpa only [d857, d405, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5490 (p : Pattern) (guard : d857 p = 1) : d406 p ≤ (0 : Int) + d63 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d406, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5489 p hg
    simpa only [d406, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d406, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5484 p hg
    simpa only [d406, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5491 (p : Pattern) (guard : d857 p = 1) : d407 p ≤ (0 : Int) + d64 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d407, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5488 p hg
    simpa only [d407, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d407, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5490 p hg
    simpa only [d407, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5492 (p : Pattern) (guard : d857 p = 1) : d408 p ≤ (0 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d408, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5486 p hg
    simpa only [d408, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d408, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5491 p hg
    simpa only [d408, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5493 (p : Pattern) (guard : d857 p = 1) : d408 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5482 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5492 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5494 (p : Pattern) (guard : d857 p = 1) : d409 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d409, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d409, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d409, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5493 p hg
    simpa only [d409, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5495 (p : Pattern) (guard : d857 p = 1) : d418 p ≤ (0 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d418, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5475 p hg
    simpa only [d418, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d418, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1762 p hg
    simpa only [d418, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5496 (p : Pattern) (guard : d857 p = 1) : d419 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d419, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5476 p hg
    simpa only [d419, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d419, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5495 p hg
    simpa only [d419, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5497 (p : Pattern) (guard : d857 p = 1) : d418 p ≤ (0 : Int) + d81 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d418, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5485 p hg
    simpa only [d418, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d418, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1762 p hg
    simpa only [d418, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5498 (p : Pattern) (guard : d857 p = 1) : d419 p ≤ (0 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d419, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5486 p hg
    simpa only [d419, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d419, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5497 p hg
    simpa only [d419, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5499 (p : Pattern) (guard : d857 p = 1) : d419 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5496 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5498 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5500 (p : Pattern) (guard : d857 p = 1) : d420 p ≤ (0 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d420, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5227 p hg
    simpa only [d420, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d420, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5499 p hg
    simpa only [d420, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5501 (p : Pattern) (guard : d857 p = 1) : d421 p ≤ (0 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d421, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5494 p hg
    simpa only [d421, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d421, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5500 p hg
    simpa only [d421, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5502 (p : Pattern) (guard : d857 p = 1) : d389 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d389, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d857, d389, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d389, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5362 p hg
    simpa only [d857, d389, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5503 (p : Pattern) (guard : d857 p = 1) : d390 p ≤ (0 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d390, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d857, d390, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d390, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5367 p hg
    simpa only [d857, d390, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5504 (p : Pattern) (guard : d857 p = 1) : d391 p ≤ (0 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d391, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5502 p hg
    simpa only [d391, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d391, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5503 p hg
    simpa only [d391, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5505 (p : Pattern) (guard : d857 p = 1) : d392 p ≤ (0 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d392, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5502 p hg
    simpa only [d392, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d392, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5504 p hg
    simpa only [d392, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5506 (p : Pattern) (guard : d857 p = 1) : d393 p ≤ (0 : Int) + d90 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d393, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d857, d393, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d393, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5371 p hg
    simpa only [d857, d393, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5507 (p : Pattern) (guard : d857 p = 1) : d394 p ≤ (0 : Int) + d91 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d394, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5502 p hg
    simpa only [d394, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d394, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5506 p hg
    simpa only [d394, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5508 (p : Pattern) (guard : d857 p = 1) : d395 p ≤ (0 : Int) + d92 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d395, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d857, d395, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d395, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5374 p hg
    simpa only [d857, d395, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5509 (p : Pattern) (guard : d857 p = 1) : d396 p ≤ (0 : Int) + d93 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d396, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5508 p hg
    simpa only [d396, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d396, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5503 p hg
    simpa only [d396, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5510 (p : Pattern) (guard : d857 p = 1) : d397 p ≤ (0 : Int) + d94 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d397, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5507 p hg
    simpa only [d397, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d397, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5509 p hg
    simpa only [d397, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5511 (p : Pattern) (guard : d857 p = 1) : d398 p ≤ (0 : Int) + d95 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d398, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5505 p hg
    simpa only [d398, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d398, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5510 p hg
    simpa only [d398, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5512 (p : Pattern) (guard : d857 p = 1) : d398 p ≤ (0 : Int) + d96 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5511 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5513 (p : Pattern) (guard : d857 p = 1) : d422 p ≤ (0 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d422, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1816 p hg
    simpa only [d857, d422, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d422, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2724 p hg
    simpa only [d857, d422, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5514 (p : Pattern) (guard : d857 p = 1) : d423 p ≤ (0 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d423, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5513 p hg
    simpa only [d423, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d423, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5221 p hg
    simpa only [d423, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5515 (p : Pattern) (guard : d857 p = 1) : d424 p ≤ (0 : Int) + d100 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d424, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5513 p hg
    simpa only [d424, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d424, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5514 p hg
    simpa only [d424, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5516 (p : Pattern) (guard : d857 p = 1) : d425 p ≤ (0 : Int) + d101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d425, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5514 p hg
    simpa only [d425, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d425, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5222 p hg
    simpa only [d425, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5517 (p : Pattern) (guard : d857 p = 1) : d426 p ≤ (0 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d426, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5515 p hg
    simpa only [d426, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d426, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5516 p hg
    simpa only [d426, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5518 (p : Pattern) (guard : d857 p = 1) : d427 p ≤ (0 : Int) + d103 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d427, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5512 p hg
    simpa only [d427, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d427, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5517 p hg
    simpa only [d427, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5519 (p : Pattern) (guard : d857 p = 1) : d415 p ≤ (0 : Int) + d104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d415, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5504 p hg
    simpa only [d415, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d415, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1762 p hg
    simpa only [d415, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5520 (p : Pattern) (guard : d857 p = 1) : d416 p ≤ (0 : Int) + d105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d416, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5505 p hg
    simpa only [d416, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d416, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5519 p hg
    simpa only [d416, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5521 (p : Pattern) (guard : d857 p = 1) : d416 p ≤ (0 : Int) + d106 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5226 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5520 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5522 (p : Pattern) (guard : d857 p = 1) : d428 p ≤ (0 : Int) + d107 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d428, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5514 p hg
    simpa only [d428, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d428, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4936 p hg
    simpa only [d428, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5523 (p : Pattern) (guard : d857 p = 1) : d429 p ≤ (0 : Int) + d108 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d429, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5515 p hg
    simpa only [d429, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d429, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5522 p hg
    simpa only [d429, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5524 (p : Pattern) (guard : d857 p = 1) : d430 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare831 p hg
    simpa only [d857, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2724 p hg
    simpa only [d857, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5525 (p : Pattern) (guard : d857 p = 1) : d431 p ≤ (0 : Int) + d109 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d431, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5524 p hg
    simpa only [d431, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d431, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1761 p hg
    simpa only [d431, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5526 (p : Pattern) (guard : d857 p = 1) : d432 p ≤ (0 : Int) + d110 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d432, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5524 p hg
    simpa only [d432, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d432, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5525 p hg
    simpa only [d432, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5527 (p : Pattern) (guard : d857 p = 1) : d433 p ≤ (0 : Int) + d111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d433, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5525 p hg
    simpa only [d433, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d433, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4936 p hg
    simpa only [d433, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5528 (p : Pattern) (guard : d857 p = 1) : d434 p ≤ (0 : Int) + d112 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d434, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5526 p hg
    simpa only [d434, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d434, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5527 p hg
    simpa only [d434, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5529 (p : Pattern) (guard : d857 p = 1) : d435 p ≤ (0 : Int) + d113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d435, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5523 p hg
    simpa only [d435, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d435, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5528 p hg
    simpa only [d435, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5530 (p : Pattern) (guard : d857 p = 1) : d436 p ≤ (0 : Int) + d114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d436, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5521 p hg
    simpa only [d436, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d436, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5529 p hg
    simpa only [d436, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5531 (p : Pattern) (guard : d857 p = 1) : d437 p ≤ (0 : Int) + d115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d437, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5518 p hg
    simpa only [d437, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d437, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5530 p hg
    simpa only [d437, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5532 (p : Pattern) (guard : d857 p = 1) : d438 p ≤ (0 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d438, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5501 p hg
    simpa only [d438, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d438, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5531 p hg
    simpa only [d438, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5533 (p : Pattern) (guard : d857 p = 1) : d439 p ≤ (0 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d439, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5226 p hg
    simpa only [d439, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d439, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5499 p hg
    simpa only [d439, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5534 (p : Pattern) (guard : d857 p = 1) : d440 p ≤ (0 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d440, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5494 p hg
    simpa only [d440, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d440, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5533 p hg
    simpa only [d440, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5535 (p : Pattern) (guard : d857 p = 1) : d441 p ≤ (0 : Int) + d120 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d441, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1494 p hg
    simpa only [d857, d441, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d441, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5371 p hg
    simpa only [d857, d441, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5536 (p : Pattern) (guard : d857 p = 1) : d442 p ≤ (0 : Int) + d121 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d442, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5502 p hg
    simpa only [d442, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d442, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5535 p hg
    simpa only [d442, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5537 (p : Pattern) (guard : d857 p = 1) : d443 p ≤ (0 : Int) + d122 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d443, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5536 p hg
    simpa only [d443, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d443, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5509 p hg
    simpa only [d443, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5538 (p : Pattern) (guard : d857 p = 1) : d444 p ≤ (0 : Int) + d123 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d444, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5505 p hg
    simpa only [d444, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d444, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5537 p hg
    simpa only [d444, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5539 (p : Pattern) (guard : d857 p = 1) : d445 p ≤ (0 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d445, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d445, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d445, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5538 p hg
    simpa only [d445, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5540 (p : Pattern) (guard : d857 p = 1) : d446 p ≤ (0 : Int) + d125 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d446, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5525 p hg
    simpa only [d446, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d446, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1762 p hg
    simpa only [d446, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5541 (p : Pattern) (guard : d857 p = 1) : d447 p ≤ (0 : Int) + d126 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d447, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5526 p hg
    simpa only [d447, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d447, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5540 p hg
    simpa only [d447, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5542 (p : Pattern) (guard : d857 p = 1) : d448 p ≤ (0 : Int) + d127 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d448, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5517 p hg
    simpa only [d448, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d448, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5541 p hg
    simpa only [d448, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5543 (p : Pattern) (guard : d857 p = 1) : d449 p ≤ (0 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d449, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5539 p hg
    simpa only [d449, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d449, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5542 p hg
    simpa only [d449, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5544 (p : Pattern) (guard : d857 p = 1) : d450 p ≤ (0 : Int) + d129 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d450, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5226 p hg
    simpa only [d450, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d450, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5498 p hg
    simpa only [d450, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5545 (p : Pattern) (guard : d857 p = 1) : d451 p ≤ (0 : Int) + d130 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d451, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5528 p hg
    simpa only [d451, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d451, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4936 p hg
    simpa only [d451, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5546 (p : Pattern) (guard : d857 p = 1) : d452 p ≤ (0 : Int) + d131 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d452, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5544 p hg
    simpa only [d452, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d452, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5545 p hg
    simpa only [d452, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5547 (p : Pattern) (guard : d857 p = 1) : d453 p ≤ (0 : Int) + d132 p := by
  cases selected : p 106 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d453, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5543 p hg
    simpa only [d453, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d453, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5546 p hg
    simpa only [d453, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5548 (p : Pattern) (guard : d857 p = 1) : d454 p ≤ (0 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d454, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5534 p hg
    simpa only [d454, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d454, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5547 p hg
    simpa only [d454, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5549 (p : Pattern) (guard : d857 p = 1) : d455 p ≤ (0 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d455, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5532 p hg
    simpa only [d455, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d455, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5548 p hg
    simpa only [d455, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5550 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5551 (p : Pattern) (guard : d1122 p = 1) : d398 p ≤ (0 : Int) + d228 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1122, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d1122, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5550 p hg
    simpa only [d1122, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5552 (p : Pattern) (guard : d1092 p = 1) : d399 p ≤ (0 : Int) + d15 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3066 p hg
    simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5553 (p : Pattern) (guard : d1092 p = 1) : d400 p ≤ (0 : Int) + d25 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3654 p hg
    simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5554 (p : Pattern) (guard : d1092 p = 1) : d401 p ≤ (0 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d401, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5552 p hg
    simpa only [d401, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d401, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5553 p hg
    simpa only [d401, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5555 (p : Pattern) (guard : d1092 p = 1) : d402 p ≤ (0 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d402, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5552 p hg
    simpa only [d402, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d402, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5554 p hg
    simpa only [d402, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5556 (p : Pattern) (guard : d1092 p = 1) : d403 p ≤ (0 : Int) + d34 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2066 p hg
    simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3657 p hg
    simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5557 (p : Pattern) (guard : d1092 p = 1) : d404 p ≤ (0 : Int) + d48 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d404, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5552 p hg
    simpa only [d404, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d404, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5556 p hg
    simpa only [d404, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5558 (p : Pattern) (guard : d1092 p = 1) : d405 p ≤ (0 : Int) + d41 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2069 p hg
    simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3068 p hg
    simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5559 (p : Pattern) (guard : d1092 p = 1) : d406 p ≤ (0 : Int) + d49 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d406, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5558 p hg
    simpa only [d406, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d406, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5553 p hg
    simpa only [d406, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5560 (p : Pattern) (guard : d1092 p = 1) : d407 p ≤ (0 : Int) + d50 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d407, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5557 p hg
    simpa only [d407, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d407, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5559 p hg
    simpa only [d407, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5561 (p : Pattern) (guard : d1092 p = 1) : d408 p ≤ (0 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d408, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5555 p hg
    simpa only [d408, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d408, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5560 p hg
    simpa only [d408, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5562 (p : Pattern) (guard : d1125 p = 1) : d408 p ≤ (0 : Int) + d229 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5561 p hg
    simpa only [d1125, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5218 p hg
    simpa only [d1125, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5563 (p : Pattern) (guard : d1126 p = 1) : d409 p ≤ (0 : Int) + d230 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d409, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5551 p hg
    simpa only [d1126, d409, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d409, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5562 p hg
    simpa only [d1126, d409, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5564 (p : Pattern) (guard : d0 p = 1) : d416 p ≤ (0 : Int) + d150 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5565 (p : Pattern) (guard : d1122 p = 1) : d417 p ≤ (0 : Int) + d231 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1122, d417, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5224 p hg
    simpa only [d1122, d417, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d417, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5564 p hg
    simpa only [d1122, d417, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5566 (p : Pattern) (guard : d1092 p = 1) : d418 p ≤ (0 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d418, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5554 p hg
    simpa only [d418, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d418, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d418, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5567 (p : Pattern) (guard : d1092 p = 1) : d419 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d419, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5555 p hg
    simpa only [d419, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d419, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5566 p hg
    simpa only [d419, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5568 (p : Pattern) (guard : d0 p = 1) : d419 p ≤ (0 : Int) + d154 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5569 (p : Pattern) (guard : d1125 p = 1) : d419 p ≤ (0 : Int) + d232 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5567 p hg
    simpa only [d1125, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5568 p hg
    simpa only [d1125, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5570 (p : Pattern) (guard : d1126 p = 1) : d420 p ≤ (0 : Int) + d233 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d420, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5565 p hg
    simpa only [d1126, d420, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d420, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5569 p hg
    simpa only [d1126, d420, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5571 (p : Pattern) (guard : d1126 p = 1) : d421 p ≤ (0 : Int) + d234 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d421, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5563 p hg
    simpa only [d421, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d421, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5570 p hg
    simpa only [d421, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5572 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (0 : Int) + d150 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5573 (p : Pattern) (guard : d1122 p = 1) : d398 p ≤ (0 : Int) + d235 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1122, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d1122, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5572 p hg
    simpa only [d1122, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5574 (p : Pattern) (guard : d1092 p = 1) : d422 p ≤ (0 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d422, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2089 p hg
    simpa only [d1092, d422, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d422, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2724 p hg
    simpa only [d1092, d422, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5575 (p : Pattern) (guard : d1092 p = 1) : d411 p ≤ (0 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d411, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2091 p hg
    simpa only [d1092, d411, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d411, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1685 p hg
    simpa only [d1092, d411, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5576 (p : Pattern) (guard : d1092 p = 1) : d423 p ≤ (0 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d423, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5574 p hg
    simpa only [d423, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d423, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5575 p hg
    simpa only [d423, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5577 (p : Pattern) (guard : d1092 p = 1) : d424 p ≤ (0 : Int) + d100 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d424, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5574 p hg
    simpa only [d424, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d424, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5576 p hg
    simpa only [d424, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5578 (p : Pattern) (guard : d1092 p = 1) : d410 p ≤ (0 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d410, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2095 p hg
    simpa only [d1092, d410, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d410, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d1092, d410, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5579 (p : Pattern) (guard : d1092 p = 1) : d412 p ≤ (0 : Int) + d72 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d412, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5578 p hg
    simpa only [d412, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d412, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5575 p hg
    simpa only [d412, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5580 (p : Pattern) (guard : d1092 p = 1) : d425 p ≤ (0 : Int) + d101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d425, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5576 p hg
    simpa only [d425, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d425, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5579 p hg
    simpa only [d425, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5581 (p : Pattern) (guard : d1092 p = 1) : d426 p ≤ (0 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d426, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5577 p hg
    simpa only [d426, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d426, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5580 p hg
    simpa only [d426, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5582 (p : Pattern) (guard : d0 p = 1) : d426 p ≤ (0 : Int) + d154 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5583 (p : Pattern) (guard : d1125 p = 1) : d426 p ≤ (0 : Int) + d236 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5581 p hg
    simpa only [d1125, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5582 p hg
    simpa only [d1125, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5584 (p : Pattern) (guard : d1126 p = 1) : d427 p ≤ (0 : Int) + d237 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d427, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5573 p hg
    simpa only [d1126, d427, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d427, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5583 p hg
    simpa only [d1126, d427, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5585 (p : Pattern) (guard : d0 p = 1) : d416 p ≤ (0 : Int) + d161 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5586 (p : Pattern) (guard : d1122 p = 1) : d416 p ≤ (0 : Int) + d238 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1122, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5226 p hg
    simpa only [d1122, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5585 p hg
    simpa only [d1122, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5587 (p : Pattern) (guard : d1092 p = 1) : d428 p ≤ (0 : Int) + d107 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d428, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5576 p hg
    simpa only [d428, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d428, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2105 p hg
    simpa only [d428, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5588 (p : Pattern) (guard : d1092 p = 1) : d429 p ≤ (0 : Int) + d108 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d429, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5577 p hg
    simpa only [d429, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d429, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5587 p hg
    simpa only [d429, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5589 (p : Pattern) (guard : d0 p = 1) : d434 p ≤ (0 : Int) + d163 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5590 (p : Pattern) (guard : d1125 p = 1) : d435 p ≤ (0 : Int) + d239 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d435, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5588 p hg
    simpa only [d1125, d435, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d435, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5589 p hg
    simpa only [d1125, d435, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5591 (p : Pattern) (guard : d1126 p = 1) : d436 p ≤ (0 : Int) + d240 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d436, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5586 p hg
    simpa only [d1126, d436, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d436, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5590 p hg
    simpa only [d1126, d436, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5592 (p : Pattern) (guard : d1126 p = 1) : d437 p ≤ (0 : Int) + d241 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d437, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5584 p hg
    simpa only [d437, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d437, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5591 p hg
    simpa only [d437, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5593 (p : Pattern) (guard : d1126 p = 1) : d438 p ≤ (0 : Int) + d242 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d438, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5571 p hg
    simpa only [d438, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d438, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5592 p hg
    simpa only [d438, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5594 (p : Pattern) (guard : d0 p = 1) : d408 p ≤ (0 : Int) + d154 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5595 (p : Pattern) (guard : d1125 p = 1) : d408 p ≤ (0 : Int) + d243 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5561 p hg
    simpa only [d1125, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5594 p hg
    simpa only [d1125, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5596 (p : Pattern) (guard : d1126 p = 1) : d409 p ≤ (0 : Int) + d244 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d409, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5573 p hg
    simpa only [d1126, d409, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d409, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5595 p hg
    simpa only [d1126, d409, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5597 (p : Pattern) (guard : d0 p = 1) : d419 p ≤ (0 : Int) + d163 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5598 (p : Pattern) (guard : d1125 p = 1) : d419 p ≤ (0 : Int) + d245 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5567 p hg
    simpa only [d1125, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5597 p hg
    simpa only [d1125, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5599 (p : Pattern) (guard : d1126 p = 1) : d439 p ≤ (0 : Int) + d246 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d439, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5586 p hg
    simpa only [d1126, d439, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d439, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5598 p hg
    simpa only [d1126, d439, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
