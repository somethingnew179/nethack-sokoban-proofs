/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons138
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare19460 (p : Pattern) (guard : d5540 p = 1) : d2218 p ≤ (0 : Int) + d5570 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2218, d5570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19430 p hg
    simpa only [d2218, d5570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2218, d5570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19459 p hg
    simpa only [d2218, d5570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19461 (p : Pattern) (guard : d5540 p = 1) : d2219 p ≤ (0 : Int) + d5571 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2219, d5571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19422 p hg
    simpa only [d2219, d5571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2219, d5571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2219, d5571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19462 (p : Pattern) (guard : d5540 p = 1) : d2220 p ≤ (0 : Int) + d5572 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2220, d5572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19460 p hg
    simpa only [d2220, d5572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2220, d5572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19461 p hg
    simpa only [d2220, d5572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19463 (p : Pattern) (guard : d5540 p = 1) : d2221 p ≤ (0 : Int) + d5573 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2221, d5573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19455 p hg
    simpa only [d2221, d5573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2221, d5573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19462 p hg
    simpa only [d2221, d5573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19464 (p : Pattern) (guard : d5540 p = 1) : d2222 p ≤ (0 : Int) + d5574 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2222, d5574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19430 p hg
    simpa only [d2222, d5574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2222, d5574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2222, d5574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19465 (p : Pattern) (guard : d5540 p = 1) : d2223 p ≤ (0 : Int) + d5575 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2223, d5575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19464 p hg
    simpa only [d2223, d5575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2223, d5575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19461 p hg
    simpa only [d2223, d5575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19466 (p : Pattern) (guard : d5540 p = 1) : d2224 p ≤ (0 : Int) + d5576 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2224, d5576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19437 p hg
    simpa only [d2224, d5576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2224, d5576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2224, d5576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19467 (p : Pattern) (guard : d5540 p = 1) : d2225 p ≤ (0 : Int) + d5577 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2225, d5577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19466 p hg
    simpa only [d2225, d5577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2225, d5577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2225, d5577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19468 (p : Pattern) (guard : d5540 p = 1) : d2226 p ≤ (0 : Int) + d5578 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2226, d5578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19465 p hg
    simpa only [d2226, d5578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2226, d5578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19467 p hg
    simpa only [d2226, d5578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19469 (p : Pattern) (guard : d5540 p = 1) : d2227 p ≤ (0 : Int) + d5579 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2227, d5579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19463 p hg
    simpa only [d2227, d5579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2227, d5579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19468 p hg
    simpa only [d2227, d5579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19470 (p : Pattern) (guard : d5540 p = 1) : d2228 p ≤ (0 : Int) + d5580 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2228, d5580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19444 p hg
    simpa only [d2228, d5580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2228, d5580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19469 p hg
    simpa only [d2228, d5580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19471 (p : Pattern) (guard : d5540 p = 1) : d2229 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19401 p hg
    simpa only [d5540, d2229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18024 p hg
    simpa only [d5540, d2229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19472 (p : Pattern) (guard : d5540 p = 1) : d2230 p ≤ (0 : Int) + d5542 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2230, d5542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19471 p hg
    simpa only [d2230, d5542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2230, d5542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19404 p hg
    simpa only [d2230, d5542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19473 (p : Pattern) (guard : d5540 p = 1) : d2231 p ≤ (0 : Int) + d5545 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2231, d5545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19472 p hg
    simpa only [d2231, d5545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2231, d5545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19409 p hg
    simpa only [d2231, d5545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19474 (p : Pattern) (guard : d5540 p = 1) : d2209 p ≤ (0 : Int) + d31 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19445 p hg
    simpa only [d5540, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5677 p hg
    simpa only [d5540, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19475 (p : Pattern) (guard : d5540 p = 1) : d2209 p ≤ (0 : Int) + d5581 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d5581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19474 p hg
    simpa only [d5581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d5581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19447 p hg
    simpa only [d5581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19476 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1743 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19477 (p : Pattern) (guard : d5540 p = 1) : d2209 p ≤ (0 : Int) + d5582 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2209, d5582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19445 p hg
    simpa only [d5540, d2209, d5582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2209, d5582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19476 p hg
    simpa only [d5540, d2209, d5582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19478 (p : Pattern) (guard : d5540 p = 1) : d2210 p ≤ (0 : Int) + d5583 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2210, d5583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19477 p hg
    simpa only [d2210, d5583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2210, d5583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2210, d5583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19479 (p : Pattern) (guard : d5540 p = 1) : d2232 p ≤ (0 : Int) + d5584 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2232, d5584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19475 p hg
    simpa only [d2232, d5584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2232, d5584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19478 p hg
    simpa only [d2232, d5584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19480 (p : Pattern) (guard : d5540 p = 1) : d2233 p ≤ (0 : Int) + d5585 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2233, d5585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19473 p hg
    simpa only [d2233, d5585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2233, d5585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19479 p hg
    simpa only [d2233, d5585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19481 (p : Pattern) (guard : d5540 p = 1) : d2234 p ≤ (0 : Int) + d5586 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2234, d5586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19426 p hg
    simpa only [d2234, d5586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2234, d5586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19441 p hg
    simpa only [d2234, d5586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19482 (p : Pattern) (guard : d5540 p = 1) : d2235 p ≤ (0 : Int) + d5587 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2235, d5587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19480 p hg
    simpa only [d2235, d5587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2235, d5587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19481 p hg
    simpa only [d2235, d5587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19483 (p : Pattern) (guard : d5501 p = 1) : d58 p ≤ (0 : Int) + d58 p := by
  omega
theorem compare19484 (p : Pattern) (guard : d5540 p = 1) : d2236 p ≤ (0 : Int) + d58 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19483 p hg
    simpa only [d5540, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5684 p hg
    simpa only [d5540, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19485 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d329 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19486 (p : Pattern) (guard : d5540 p = 1) : d2236 p ≤ (0 : Int) + d5588 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2236, d5588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19483 p hg
    simpa only [d5540, d2236, d5588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2236, d5588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19485 p hg
    simpa only [d5540, d2236, d5588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19487 (p : Pattern) (guard : d5540 p = 1) : d2236 p ≤ (0 : Int) + d5589 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d5589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19484 p hg
    simpa only [d5589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d5589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19486 p hg
    simpa only [d5589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19488 (p : Pattern) (guard : d5540 p = 1) : d2237 p ≤ (0 : Int) + d5590 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2237, d5590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19486 p hg
    simpa only [d2237, d5590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2237, d5590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2237, d5590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19489 (p : Pattern) (guard : d5540 p = 1) : d2238 p ≤ (0 : Int) + d5591 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2238, d5591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19487 p hg
    simpa only [d2238, d5591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2238, d5591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19488 p hg
    simpa only [d2238, d5591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19490 (p : Pattern) (guard : d5540 p = 1) : d2239 p ≤ (0 : Int) + d5592 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2239, d5592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19426 p hg
    simpa only [d2239, d5592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2239, d5592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19489 p hg
    simpa only [d2239, d5592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19491 (p : Pattern) (guard : d5540 p = 1) : d2216 p ≤ (0 : Int) + d40 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19456 p hg
    simpa only [d5540, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5689 p hg
    simpa only [d5540, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19492 (p : Pattern) (guard : d5540 p = 1) : d2216 p ≤ (0 : Int) + d5593 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d5593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19491 p hg
    simpa only [d5593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d5593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19458 p hg
    simpa only [d5593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19493 (p : Pattern) (guard : d5540 p = 1) : d2240 p ≤ (0 : Int) + d5594 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2240, d5594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19492 p hg
    simpa only [d2240, d5594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2240, d5594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19459 p hg
    simpa only [d2240, d5594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19494 (p : Pattern) (guard : d5540 p = 1) : d2241 p ≤ (0 : Int) + d5595 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2241, d5595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19493 p hg
    simpa only [d2241, d5595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2241, d5595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2241, d5595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19495 (p : Pattern) (guard : d5540 p = 1) : d2242 p ≤ (0 : Int) + d5596 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2242, d5596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19490 p hg
    simpa only [d2242, d5596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2242, d5596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19494 p hg
    simpa only [d2242, d5596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19496 (p : Pattern) (guard : d5540 p = 1) : d2243 p ≤ (0 : Int) + d5597 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2243, d5597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19482 p hg
    simpa only [d2243, d5597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2243, d5597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19495 p hg
    simpa only [d2243, d5597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19497 (p : Pattern) (guard : d5540 p = 1) : d2244 p ≤ (0 : Int) + d5598 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2244, d5598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19475 p hg
    simpa only [d2244, d5598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2244, d5598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2244, d5598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19498 (p : Pattern) (guard : d5540 p = 1) : d2245 p ≤ (0 : Int) + d5599 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2245, d5599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19454 p hg
    simpa only [d2245, d5599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2245, d5599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19497 p hg
    simpa only [d2245, d5599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19499 (p : Pattern) (guard : d5540 p = 1) : d2246 p ≤ (0 : Int) + d5600 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2246, d5600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19461 p hg
    simpa only [d2246, d5600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2246, d5600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19466 p hg
    simpa only [d2246, d5600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19500 (p : Pattern) (guard : d5540 p = 1) : d2247 p ≤ (0 : Int) + d5601 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2247, d5601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19498 p hg
    simpa only [d2247, d5601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2247, d5601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19499 p hg
    simpa only [d2247, d5601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19501 (p : Pattern) (guard : d5540 p = 1) : d2248 p ≤ (0 : Int) + d5602 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2248, d5602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19487 p hg
    simpa only [d2248, d5602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2248, d5602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2248, d5602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19502 (p : Pattern) (guard : d5540 p = 1) : d2249 p ≤ (0 : Int) + d5603 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2249, d5603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19461 p hg
    simpa only [d2249, d5603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2249, d5603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19501 p hg
    simpa only [d2249, d5603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19503 (p : Pattern) (guard : d5540 p = 1) : d2250 p ≤ (0 : Int) + d5604 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2250, d5604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19492 p hg
    simpa only [d2250, d5604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2250, d5604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2250, d5604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19504 (p : Pattern) (guard : d5540 p = 1) : d2251 p ≤ (0 : Int) + d5605 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2251, d5605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19503 p hg
    simpa only [d2251, d5605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2251, d5605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2251, d5605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19505 (p : Pattern) (guard : d5540 p = 1) : d2252 p ≤ (0 : Int) + d5606 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2252, d5606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19502 p hg
    simpa only [d2252, d5606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2252, d5606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19504 p hg
    simpa only [d2252, d5606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19506 (p : Pattern) (guard : d5540 p = 1) : d2253 p ≤ (0 : Int) + d5607 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2253, d5607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19500 p hg
    simpa only [d2253, d5607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2253, d5607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19505 p hg
    simpa only [d2253, d5607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19507 (p : Pattern) (guard : d5540 p = 1) : d2254 p ≤ (0 : Int) + d5608 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2254, d5608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19496 p hg
    simpa only [d2254, d5608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2254, d5608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19506 p hg
    simpa only [d2254, d5608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19508 (p : Pattern) (guard : d5540 p = 1) : d2255 p ≤ (0 : Int) + d5609 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2255, d5609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19470 p hg
    simpa only [d2255, d5609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2255, d5609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19507 p hg
    simpa only [d2255, d5609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19509 (p : Pattern) (guard : d5540 p = 1) : d2187 p ≤ (0 : Int) + d5610 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2187, d5610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19404 p hg
    simpa only [d2187, d5610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2187, d5610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2187, d5610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19510 (p : Pattern) (guard : d5540 p = 1) : d2201 p ≤ (0 : Int) + d5611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2201, d5611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19430 p hg
    simpa only [d2201, d5611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2201, d5611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19509 p hg
    simpa only [d2201, d5611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19511 (p : Pattern) (guard : d5540 p = 1) : d2197 p ≤ (0 : Int) + d5612 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2197, d5612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19421 p hg
    simpa only [d2197, d5612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2197, d5612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2197, d5612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19512 (p : Pattern) (guard : d5540 p = 1) : d2198 p ≤ (0 : Int) + d5613 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2198, d5613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19422 p hg
    simpa only [d2198, d5613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2198, d5613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19511 p hg
    simpa only [d2198, d5613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19513 (p : Pattern) (guard : d5540 p = 1) : d2202 p ≤ (0 : Int) + d5614 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2202, d5614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19510 p hg
    simpa only [d2202, d5614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2202, d5614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19512 p hg
    simpa only [d2202, d5614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19514 (p : Pattern) (guard : d5540 p = 1) : d2256 p ≤ (0 : Int) + d5615 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2256, d5615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19510 p hg
    simpa only [d2256, d5615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2256, d5615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19513 p hg
    simpa only [d2256, d5615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19515 (p : Pattern) (guard : d5540 p = 1) : d2204 p ≤ (0 : Int) + d5616 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2204, d5616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19436 p hg
    simpa only [d2204, d5616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2204, d5616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2204, d5616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19516 (p : Pattern) (guard : d5540 p = 1) : d2205 p ≤ (0 : Int) + d5617 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2205, d5617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19437 p hg
    simpa only [d2205, d5617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2205, d5617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19515 p hg
    simpa only [d2205, d5617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19517 (p : Pattern) (guard : d5540 p = 1) : d2206 p ≤ (0 : Int) + d5618 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2206, d5618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19516 p hg
    simpa only [d2206, d5618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2206, d5618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2206, d5618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19518 (p : Pattern) (guard : d5540 p = 1) : d2207 p ≤ (0 : Int) + d5619 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2207, d5619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19513 p hg
    simpa only [d2207, d5619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2207, d5619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19517 p hg
    simpa only [d2207, d5619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19519 (p : Pattern) (guard : d5540 p = 1) : d2257 p ≤ (0 : Int) + d5620 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2257, d5620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19514 p hg
    simpa only [d2257, d5620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2257, d5620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19518 p hg
    simpa only [d2257, d5620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19520 (p : Pattern) (guard : d5540 p = 1) : d2232 p ≤ (0 : Int) + d5621 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2232, d5621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19475 p hg
    simpa only [d2232, d5621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2232, d5621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19448 p hg
    simpa only [d2232, d5621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19521 (p : Pattern) (guard : d5540 p = 1) : d2212 p ≤ (0 : Int) + d35 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19450 p hg
    simpa only [d5540, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5808 p hg
    simpa only [d5540, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19522 (p : Pattern) (guard : d5540 p = 1) : d2212 p ≤ (0 : Int) + d5622 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d5622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19521 p hg
    simpa only [d5622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d5622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19452 p hg
    simpa only [d5622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19523 (p : Pattern) (guard : d5540 p = 1) : d2258 p ≤ (0 : Int) + d5623 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2258, d5623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19522 p hg
    simpa only [d2258, d5623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2258, d5623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19453 p hg
    simpa only [d2258, d5623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19524 (p : Pattern) (guard : d5540 p = 1) : d2259 p ≤ (0 : Int) + d5624 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2259, d5624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19520 p hg
    simpa only [d2259, d5624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2259, d5624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19523 p hg
    simpa only [d2259, d5624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19525 (p : Pattern) (guard : d5540 p = 1) : d2260 p ≤ (0 : Int) + d5625 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2260, d5625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19524 p hg
    simpa only [d2260, d5625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2260, d5625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19494 p hg
    simpa only [d2260, d5625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19526 (p : Pattern) (guard : d5540 p = 1) : d2261 p ≤ (0 : Int) + d5626 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2261, d5626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19525 p hg
    simpa only [d2261, d5626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2261, d5626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2261, d5626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19527 (p : Pattern) (guard : d5540 p = 1) : d2262 p ≤ (0 : Int) + d5627 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2262, d5627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19519 p hg
    simpa only [d2262, d5627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2262, d5627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19526 p hg
    simpa only [d2262, d5627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19528 (p : Pattern) (guard : d5540 p = 1) : d2263 p ≤ (0 : Int) + d5628 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2263, d5628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19510 p hg
    simpa only [d2263, d5628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2263, d5628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19520 p hg
    simpa only [d2263, d5628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19529 (p : Pattern) (guard : d5540 p = 1) : d2234 p ≤ (0 : Int) + d5629 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2234, d5629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19512 p hg
    simpa only [d2234, d5629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2234, d5629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19516 p hg
    simpa only [d2234, d5629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19530 (p : Pattern) (guard : d5540 p = 1) : d2264 p ≤ (0 : Int) + d5630 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2264, d5630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19528 p hg
    simpa only [d2264, d5630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2264, d5630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19529 p hg
    simpa only [d2264, d5630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19531 (p : Pattern) (guard : d5540 p = 1) : d2239 p ≤ (0 : Int) + d5631 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2239, d5631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19512 p hg
    simpa only [d2239, d5631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2239, d5631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19489 p hg
    simpa only [d2239, d5631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19532 (p : Pattern) (guard : d5540 p = 1) : d2242 p ≤ (0 : Int) + d5632 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2242, d5632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19531 p hg
    simpa only [d2242, d5632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2242, d5632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19494 p hg
    simpa only [d2242, d5632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19533 (p : Pattern) (guard : d5540 p = 1) : d2265 p ≤ (0 : Int) + d5633 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2265, d5633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19530 p hg
    simpa only [d2265, d5633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2265, d5633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19532 p hg
    simpa only [d2265, d5633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19534 (p : Pattern) (guard : d5540 p = 1) : d2266 p ≤ (0 : Int) + d5634 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2266, d5634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19523 p hg
    simpa only [d2266, d5634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2266, d5634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2266, d5634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19535 (p : Pattern) (guard : d5540 p = 1) : d2267 p ≤ (0 : Int) + d5635 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2267, d5635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19534 p hg
    simpa only [d2267, d5635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2267, d5635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2267, d5635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19536 (p : Pattern) (guard : d5540 p = 1) : d2268 p ≤ (0 : Int) + d5636 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2268, d5636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19535 p hg
    simpa only [d2268, d5636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2268, d5636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2268, d5636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19537 (p : Pattern) (guard : d5540 p = 1) : d2269 p ≤ (0 : Int) + d5637 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2269, d5637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19533 p hg
    simpa only [d2269, d5637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2269, d5637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19536 p hg
    simpa only [d2269, d5637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19538 (p : Pattern) (guard : d5540 p = 1) : d2270 p ≤ (0 : Int) + d5638 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2270, d5638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19527 p hg
    simpa only [d2270, d5638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2270, d5638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19537 p hg
    simpa only [d2270, d5638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19539 (p : Pattern) (guard : d5540 p = 1) : d2271 p ≤ (0 : Int) + d5639 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2271, d5639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19508 p hg
    simpa only [d2271, d5639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2271, d5639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19538 p hg
    simpa only [d2271, d5639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19540 (p : Pattern) (guard : d5540 p = 1) : d2195 p ≤ (0 : Int) + d5611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2195, d5611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19416 p hg
    simpa only [d2195, d5611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2195, d5611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19509 p hg
    simpa only [d2195, d5611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19541 (p : Pattern) (guard : d5540 p = 1) : d2272 p ≤ (0 : Int) + d5611 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19540 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19510 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19542 (p : Pattern) (guard : d5540 p = 1) : d2273 p ≤ (0 : Int) + d5615 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2273, d5615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19541 p hg
    simpa only [d2273, d5615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2273, d5615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19513 p hg
    simpa only [d2273, d5615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19543 (p : Pattern) (guard : d5540 p = 1) : d2274 p ≤ (0 : Int) + d5620 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2274, d5620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19542 p hg
    simpa only [d2274, d5620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2274, d5620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19518 p hg
    simpa only [d2274, d5620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19544 (p : Pattern) (guard : d5540 p = 1) : d2275 p ≤ (0 : Int) + d5627 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2275, d5627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19543 p hg
    simpa only [d2275, d5627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2275, d5627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19526 p hg
    simpa only [d2275, d5627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19545 (p : Pattern) (guard : d5540 p = 1) : d2276 p ≤ (0 : Int) + d5638 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2276, d5638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19544 p hg
    simpa only [d2276, d5638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2276, d5638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19537 p hg
    simpa only [d2276, d5638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19546 (p : Pattern) (guard : d5540 p = 1) : d2277 p ≤ (0 : Int) + d5640 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2277, d5640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19516 p hg
    simpa only [d2277, d5640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2277, d5640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19493 p hg
    simpa only [d2277, d5640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19547 (p : Pattern) (guard : d5540 p = 1) : d2278 p ≤ (0 : Int) + d5641 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2278, d5641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19546 p hg
    simpa only [d2278, d5641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2278, d5641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19494 p hg
    simpa only [d2278, d5641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19548 (p : Pattern) (guard : d5540 p = 1) : d2279 p ≤ (0 : Int) + d5642 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2279, d5642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19494 p hg
    simpa only [d2279, d5642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2279, d5642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2279, d5642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19549 (p : Pattern) (guard : d5540 p = 1) : d2280 p ≤ (0 : Int) + d5643 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2280, d5643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19547 p hg
    simpa only [d2280, d5643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2280, d5643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19548 p hg
    simpa only [d2280, d5643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19550 (p : Pattern) (guard : d5540 p = 1) : d2281 p ≤ (0 : Int) + d5644 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2281, d5644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19548 p hg
    simpa only [d2281, d5644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2281, d5644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2281, d5644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19551 (p : Pattern) (guard : d5540 p = 1) : d2282 p ≤ (0 : Int) + d5645 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2282, d5645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19549 p hg
    simpa only [d2282, d5645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2282, d5645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19550 p hg
    simpa only [d2282, d5645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19552 (p : Pattern) (guard : d5540 p = 1) : d2283 p ≤ (0 : Int) + d5646 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2283, d5646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19550 p hg
    simpa only [d2283, d5646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2283, d5646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2283, d5646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19553 (p : Pattern) (guard : d5540 p = 1) : d2284 p ≤ (0 : Int) + d5647 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2284, d5647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19551 p hg
    simpa only [d2284, d5647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2284, d5647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19552 p hg
    simpa only [d2284, d5647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19554 (p : Pattern) (guard : d5540 p = 1) : d2285 p ≤ (0 : Int) + d5648 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2285, d5648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19545 p hg
    simpa only [d2285, d5648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2285, d5648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19553 p hg
    simpa only [d2285, d5648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19555 (p : Pattern) (guard : d5540 p = 1) : d2286 p ≤ (0 : Int) + d5649 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2286, d5649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19539 p hg
    simpa only [d2286, d5649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2286, d5649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19554 p hg
    simpa only [d2286, d5649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19556 (p : Pattern) (guard : d5540 p = 1) : d2287 p ≤ (0 : Int) + d5545 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19413 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19431 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19557 (p : Pattern) (guard : d5540 p = 1) : d2288 p ≤ (0 : Int) + d5552 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2288, d5552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19556 p hg
    simpa only [d2288, d5552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2288, d5552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19432 p hg
    simpa only [d2288, d5552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19558 (p : Pattern) (guard : d5540 p = 1) : d2289 p ≤ (0 : Int) + d5560 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2289, d5560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19557 p hg
    simpa only [d2289, d5560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2289, d5560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19443 p hg
    simpa only [d2289, d5560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19559 (p : Pattern) (guard : d5540 p = 1) : d2290 p ≤ (0 : Int) + d5580 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2290, d5580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19558 p hg
    simpa only [d2290, d5580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2290, d5580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19469 p hg
    simpa only [d2290, d5580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19560 (p : Pattern) (guard : d5540 p = 1) : d2263 p ≤ (0 : Int) + d5585 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2263, d5585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19431 p hg
    simpa only [d2263, d5585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2263, d5585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19479 p hg
    simpa only [d2263, d5585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19561 (p : Pattern) (guard : d5540 p = 1) : d2264 p ≤ (0 : Int) + d5587 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2264, d5587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19560 p hg
    simpa only [d2264, d5587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2264, d5587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19481 p hg
    simpa only [d2264, d5587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19562 (p : Pattern) (guard : d5540 p = 1) : d2265 p ≤ (0 : Int) + d5597 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2265, d5597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19561 p hg
    simpa only [d2265, d5597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2265, d5597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19495 p hg
    simpa only [d2265, d5597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19563 (p : Pattern) (guard : d5540 p = 1) : d2291 p ≤ (0 : Int) + d5608 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2291, d5608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19562 p hg
    simpa only [d2291, d5608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2291, d5608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19506 p hg
    simpa only [d2291, d5608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19564 (p : Pattern) (guard : d5540 p = 1) : d2292 p ≤ (0 : Int) + d5609 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2292, d5609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19559 p hg
    simpa only [d2292, d5609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2292, d5609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19563 p hg
    simpa only [d2292, d5609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19565 (p : Pattern) (guard : d5540 p = 1) : d2293 p ≤ (0 : Int) + d5639 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2293, d5639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19564 p hg
    simpa only [d2293, d5639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2293, d5639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19538 p hg
    simpa only [d2293, d5639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19566 (p : Pattern) (guard : d5540 p = 1) : d2294 p ≤ (0 : Int) + d5650 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2294, d5650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19538 p hg
    simpa only [d2294, d5650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2294, d5650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2294, d5650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19567 (p : Pattern) (guard : d5540 p = 1) : d2295 p ≤ (0 : Int) + d5651 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2295, d5651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19565 p hg
    simpa only [d2295, d5651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2295, d5651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19566 p hg
    simpa only [d2295, d5651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19568 (p : Pattern) (guard : d5540 p = 1) : d2296 p ≤ (0 : Int) + d5652 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2296, d5652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19555 p hg
    simpa only [d2296, d5652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2296, d5652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19567 p hg
    simpa only [d2296, d5652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19569 (p : Pattern) (guard : d5540 p = 1) : d2297 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19401 p hg
    simpa only [d5540, d2297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18093 p hg
    simpa only [d5540, d2297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19570 (p : Pattern) (guard : d5540 p = 1) : d2298 p ≤ (0 : Int) + d5542 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2298, d5542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19569 p hg
    simpa only [d2298, d5542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2298, d5542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19404 p hg
    simpa only [d2298, d5542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19571 (p : Pattern) (guard : d5540 p = 1) : d2299 p ≤ (0 : Int) + d5545 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2299, d5545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19570 p hg
    simpa only [d2299, d5545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2299, d5545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19409 p hg
    simpa only [d2299, d5545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19572 (p : Pattern) (guard : d5540 p = 1) : d2300 p ≤ (0 : Int) + d5545 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19571 p hg
    simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19417 p hg
    simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19573 (p : Pattern) (guard : d5540 p = 1) : d2301 p ≤ (0 : Int) + d5552 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2301, d5552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19572 p hg
    simpa only [d2301, d5552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2301, d5552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19432 p hg
    simpa only [d2301, d5552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19574 (p : Pattern) (guard : d5540 p = 1) : d2302 p ≤ (0 : Int) + d5560 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2302, d5560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19573 p hg
    simpa only [d2302, d5560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2302, d5560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19443 p hg
    simpa only [d2302, d5560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19575 (p : Pattern) (guard : d5540 p = 1) : d2303 p ≤ (0 : Int) + d5580 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2303, d5580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19574 p hg
    simpa only [d2303, d5580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2303, d5580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19469 p hg
    simpa only [d2303, d5580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19576 (p : Pattern) (guard : d5540 p = 1) : d2304 p ≤ (0 : Int) + d5585 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2304, d5585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19413 p hg
    simpa only [d2304, d5585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2304, d5585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19479 p hg
    simpa only [d2304, d5585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19577 (p : Pattern) (guard : d5540 p = 1) : d2305 p ≤ (0 : Int) + d5587 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2305, d5587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19576 p hg
    simpa only [d2305, d5587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2305, d5587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19481 p hg
    simpa only [d2305, d5587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19578 (p : Pattern) (guard : d5540 p = 1) : d2306 p ≤ (0 : Int) + d5597 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2306, d5597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19577 p hg
    simpa only [d2306, d5597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2306, d5597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19495 p hg
    simpa only [d2306, d5597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19579 (p : Pattern) (guard : d5540 p = 1) : d2307 p ≤ (0 : Int) + d5608 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2307, d5608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19578 p hg
    simpa only [d2307, d5608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2307, d5608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19506 p hg
    simpa only [d2307, d5608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19580 (p : Pattern) (guard : d5540 p = 1) : d2308 p ≤ (0 : Int) + d5609 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2308, d5609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19575 p hg
    simpa only [d2308, d5609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2308, d5609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19579 p hg
    simpa only [d2308, d5609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19581 (p : Pattern) (guard : d5540 p = 1) : d2309 p ≤ (0 : Int) + d5639 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2309, d5639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19580 p hg
    simpa only [d2309, d5639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2309, d5639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19538 p hg
    simpa only [d2309, d5639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19582 (p : Pattern) (guard : d5540 p = 1) : d2310 p ≤ (0 : Int) + d5648 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2310, d5648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19538 p hg
    simpa only [d2310, d5648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2310, d5648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19553 p hg
    simpa only [d2310, d5648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19583 (p : Pattern) (guard : d5540 p = 1) : d2311 p ≤ (0 : Int) + d5649 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2311, d5649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19581 p hg
    simpa only [d2311, d5649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2311, d5649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19582 p hg
    simpa only [d2311, d5649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19584 (p : Pattern) (guard : d5540 p = 1) : d2272 p ≤ (0 : Int) + d5545 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19417 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19431 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19585 (p : Pattern) (guard : d5540 p = 1) : d2273 p ≤ (0 : Int) + d5552 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2273, d5552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19584 p hg
    simpa only [d2273, d5552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2273, d5552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19432 p hg
    simpa only [d2273, d5552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19586 (p : Pattern) (guard : d5540 p = 1) : d2274 p ≤ (0 : Int) + d5560 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2274, d5560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19585 p hg
    simpa only [d2274, d5560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2274, d5560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19443 p hg
    simpa only [d2274, d5560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19587 (p : Pattern) (guard : d5540 p = 1) : d2312 p ≤ (0 : Int) + d5580 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2312, d5580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19586 p hg
    simpa only [d2312, d5580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2312, d5580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19469 p hg
    simpa only [d2312, d5580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19588 (p : Pattern) (guard : d5540 p = 1) : d2313 p ≤ (0 : Int) + d5609 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2313, d5609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19587 p hg
    simpa only [d2313, d5609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2313, d5609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19563 p hg
    simpa only [d2313, d5609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19589 (p : Pattern) (guard : d5540 p = 1) : d2314 p ≤ (0 : Int) + d5639 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2314, d5639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19588 p hg
    simpa only [d2314, d5639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2314, d5639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19538 p hg
    simpa only [d2314, d5639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19590 (p : Pattern) (guard : d5540 p = 1) : d2315 p ≤ (0 : Int) + d5651 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2315, d5651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19589 p hg
    simpa only [d2315, d5651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2315, d5651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19566 p hg
    simpa only [d2315, d5651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19591 (p : Pattern) (guard : d5540 p = 1) : d2316 p ≤ (0 : Int) + d5652 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2316, d5652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19583 p hg
    simpa only [d2316, d5652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2316, d5652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19590 p hg
    simpa only [d2316, d5652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19592 (p : Pattern) (guard : d5540 p = 1) : d2317 p ≤ (0 : Int) + d5652 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19568 p hg
    simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19591 p hg
    simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19593 (p : Pattern) (guard : d5501 p = 1) : d103 p ≤ (0 : Int) + d103 p := by
  omega
theorem compare19594 (p : Pattern) (guard : d5540 p = 1) : d2318 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19593 p hg
    simpa only [d5540, d2318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18115 p hg
    simpa only [d5540, d2318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19595 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1940 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19596 (p : Pattern) (guard : d5540 p = 1) : d2319 p ≤ (0 : Int) + d5653 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2319, d5653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19593 p hg
    simpa only [d5540, d2319, d5653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2319, d5653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19595 p hg
    simpa only [d5540, d2319, d5653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19597 (p : Pattern) (guard : d5540 p = 1) : d2320 p ≤ (0 : Int) + d5654 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2320, d5654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19594 p hg
    simpa only [d2320, d5654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2320, d5654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19596 p hg
    simpa only [d2320, d5654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19598 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1873 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19599 (p : Pattern) (guard : d5540 p = 1) : d2319 p ≤ (0 : Int) + d5655 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2319, d5655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19593 p hg
    simpa only [d5540, d2319, d5655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2319, d5655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19598 p hg
    simpa only [d5540, d2319, d5655, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
