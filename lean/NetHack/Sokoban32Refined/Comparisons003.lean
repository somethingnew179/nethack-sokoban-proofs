/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare420 (p : Pattern) (guard : d835 p = 1) : d67 p ≤ (0 : Int) + d184 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d67, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d835, d67, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d67, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare419 p hg
    simpa only [d835, d67, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare421 (p : Pattern) (guard : d1 p = 1) : d78 p ≤ (0 : Int) + d78 p := by
  omega
theorem compare422 (p : Pattern) (guard : d0 p = 1) : d83 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare423 (p : Pattern) (guard : d835 p = 1) : d84 p ≤ (0 : Int) + d185 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d84, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare421 p hg
    simpa only [d835, d84, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d84, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare422 p hg
    simpa only [d835, d84, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare424 (p : Pattern) (guard : d835 p = 1) : d85 p ≤ (0 : Int) + d186 p := by
  cases selected : p 106 with
  | false =>
    have hg : d835 p = 1 := by simpa only [d85, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare420 p hg
    simpa only [d85, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d85, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare423 p hg
    simpa only [d85, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare425 (p : Pattern) (guard : d0 p = 1) : d166 p ≤ (0 : Int) + d206 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare426 (p : Pattern) (guard : d854 p = 1) : d174 p ≤ (0 : Int) + d207 p := by
  cases selected : p 86 with
  | false =>
    have hg : d835 p = 1 := by simpa only [d854, d174, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare424 p hg
    simpa only [d854, d174, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d174, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare425 p hg
    simpa only [d854, d174, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare427 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare428 (p : Pattern) (guard : d835 p = 1) : d67 p ≤ (0 : Int) + d208 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d67, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d835, d67, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d67, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare427 p hg
    simpa only [d835, d67, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare429 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (0 : Int) + d77 p := by
  omega
theorem compare430 (p : Pattern) (guard : d0 p = 1) : d83 p ≤ (0 : Int) + d164 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare431 (p : Pattern) (guard : d835 p = 1) : d117 p ≤ (0 : Int) + d209 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d117, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare429 p hg
    simpa only [d835, d117, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d117, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare430 p hg
    simpa only [d835, d117, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare432 (p : Pattern) (guard : d835 p = 1) : d118 p ≤ (0 : Int) + d210 p := by
  cases selected : p 106 with
  | false =>
    have hg : d835 p = 1 := by simpa only [d118, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare428 p hg
    simpa only [d118, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d118, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare431 p hg
    simpa only [d118, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare433 (p : Pattern) (guard : d0 p = 1) : d171 p ≤ (0 : Int) + d225 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare434 (p : Pattern) (guard : d854 p = 1) : d175 p ≤ (0 : Int) + d226 p := by
  cases selected : p 86 with
  | false =>
    have hg : d835 p = 1 := by simpa only [d854, d175, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare432 p hg
    simpa only [d854, d175, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d175, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare433 p hg
    simpa only [d854, d175, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare435 (p : Pattern) (guard : d854 p = 1) : d176 p ≤ (0 : Int) + d227 p := by
  cases selected : p 80 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d176, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare426 p hg
    simpa only [d176, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d176, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare434 p hg
    simpa only [d176, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare436 (p : Pattern) (guard : d0 p = 1) : d45 p ≤ (0 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare437 (p : Pattern) (guard : d857 p = 1) : d51 p ≤ (0 : Int) + d51 p := by
  omega
theorem compare438 (p : Pattern) (guard : d0 p = 1) : d52 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare439 (p : Pattern) (guard : d857 p = 1) : d53 p ≤ (0 : Int) + d15 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d857, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare438 p hg
    simpa only [d857, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare440 (p : Pattern) (guard : d0 p = 1) : d54 p ≤ (0 : Int) + d25 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare441 (p : Pattern) (guard : d857 p = 1) : d55 p ≤ (0 : Int) + d25 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare217 p hg
    simpa only [d857, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare440 p hg
    simpa only [d857, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare442 (p : Pattern) (guard : d857 p = 1) : d56 p ≤ (0 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d56, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare439 p hg
    simpa only [d56, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d56, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare441 p hg
    simpa only [d56, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare443 (p : Pattern) (guard : d857 p = 1) : d57 p ≤ (0 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d57, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare439 p hg
    simpa only [d57, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d57, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare442 p hg
    simpa only [d57, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare444 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (0 : Int) + d34 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare445 (p : Pattern) (guard : d857 p = 1) : d59 p ≤ (0 : Int) + d34 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare229 p hg
    simpa only [d857, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare444 p hg
    simpa only [d857, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare446 (p : Pattern) (guard : d857 p = 1) : d60 p ≤ (0 : Int) + d48 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d60, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare439 p hg
    simpa only [d60, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d60, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare445 p hg
    simpa only [d60, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare447 (p : Pattern) (guard : d0 p = 1) : d61 p ≤ (0 : Int) + d41 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare448 (p : Pattern) (guard : d857 p = 1) : d62 p ≤ (0 : Int) + d41 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare236 p hg
    simpa only [d857, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare447 p hg
    simpa only [d857, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare449 (p : Pattern) (guard : d857 p = 1) : d63 p ≤ (0 : Int) + d49 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d63, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare448 p hg
    simpa only [d63, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d63, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare441 p hg
    simpa only [d63, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare450 (p : Pattern) (guard : d857 p = 1) : d64 p ≤ (0 : Int) + d50 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d64, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare446 p hg
    simpa only [d64, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d64, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare449 p hg
    simpa only [d64, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare451 (p : Pattern) (guard : d857 p = 1) : d65 p ≤ (0 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d65, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare443 p hg
    simpa only [d65, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d65, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare450 p hg
    simpa only [d65, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare452 (p : Pattern) (guard : d857 p = 1) : d66 p ≤ (0 : Int) + d51 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare437 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare451 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare453 (p : Pattern) (guard : d858 p = 1) : d67 p ≤ (0 : Int) + d51 p := by
  cases selected : p 112 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d858, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare436 p hg
    simpa only [d858, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d858, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare452 p hg
    simpa only [d858, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare454 (p : Pattern) (guard : d0 p = 1) : d78 p ≤ (0 : Int) + d80 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare455 (p : Pattern) (guard : d857 p = 1) : d80 p ≤ (0 : Int) + d80 p := by
  omega
theorem compare456 (p : Pattern) (guard : d857 p = 1) : d75 p ≤ (0 : Int) + d75 p := by
  omega
theorem compare457 (p : Pattern) (guard : d857 p = 1) : d81 p ≤ (0 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d81, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare442 p hg
    simpa only [d81, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d81, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare456 p hg
    simpa only [d81, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare458 (p : Pattern) (guard : d857 p = 1) : d82 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d82, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare443 p hg
    simpa only [d82, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d82, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare457 p hg
    simpa only [d82, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare459 (p : Pattern) (guard : d857 p = 1) : d83 p ≤ (0 : Int) + d80 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare455 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare458 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare460 (p : Pattern) (guard : d858 p = 1) : d84 p ≤ (0 : Int) + d80 p := by
  cases selected : p 112 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d858, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare454 p hg
    simpa only [d858, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d858, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare459 p hg
    simpa only [d858, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare461 (p : Pattern) (guard : d858 p = 1) : d85 p ≤ (0 : Int) + d860 p := by
  cases selected : p 106 with
  | false =>
    have hg : d858 p = 1 := by simpa only [d85, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare453 p hg
    simpa only [d85, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d858 p = 1 := by simpa only [d85, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare460 p hg
    simpa only [d85, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare462 (p : Pattern) (guard : d0 p = 1) : d166 p ≤ (0 : Int) + d863 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare463 (p : Pattern) (guard : d859 p = 1) : d174 p ≤ (0 : Int) + d864 p := by
  cases selected : p 86 with
  | false =>
    have hg : d858 p = 1 := by simpa only [d859, d174, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare461 p hg
    simpa only [d859, d174, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d859, d174, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare462 p hg
    simpa only [d859, d174, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare464 (p : Pattern) (guard : d0 p = 1) : d77 p ≤ (0 : Int) + d80 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare465 (p : Pattern) (guard : d858 p = 1) : d117 p ≤ (0 : Int) + d80 p := by
  cases selected : p 112 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d858, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare464 p hg
    simpa only [d858, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d858, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare459 p hg
    simpa only [d858, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare466 (p : Pattern) (guard : d858 p = 1) : d118 p ≤ (0 : Int) + d860 p := by
  cases selected : p 106 with
  | false =>
    have hg : d858 p = 1 := by simpa only [d118, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare453 p hg
    simpa only [d118, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d858 p = 1 := by simpa only [d118, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare465 p hg
    simpa only [d118, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare467 (p : Pattern) (guard : d0 p = 1) : d171 p ≤ (0 : Int) + d863 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare468 (p : Pattern) (guard : d859 p = 1) : d175 p ≤ (0 : Int) + d864 p := by
  cases selected : p 86 with
  | false =>
    have hg : d858 p = 1 := by simpa only [d859, d175, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare466 p hg
    simpa only [d859, d175, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d859, d175, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare467 p hg
    simpa only [d859, d175, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare469 (p : Pattern) (guard : d859 p = 1) : d176 p ≤ (0 : Int) + d864 p := by
  cases selected : p 80 with
  | false =>
    have hg : d859 p = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare463 p hg
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d859 p = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare468 p hg
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare470 (p : Pattern) (guard : d0 p = 1) : d45 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare471 (p : Pattern) (guard : d866 p = 1) : d45 p ≤ (0 : Int) + d228 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d866, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare470 p hg
    simpa only [d866, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare472 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d229 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare473 (p : Pattern) (guard : d868 p = 1) : d67 p ≤ (0 : Int) + d230 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d67, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare471 p hg
    simpa only [d868, d67, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d67, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare472 p hg
    simpa only [d868, d67, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare474 (p : Pattern) (guard : d1 p = 1) : d74 p ≤ (0 : Int) + d74 p := by
  omega
theorem compare475 (p : Pattern) (guard : d0 p = 1) : d77 p ≤ (0 : Int) + d150 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare476 (p : Pattern) (guard : d866 p = 1) : d78 p ≤ (0 : Int) + d231 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d78, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare474 p hg
    simpa only [d866, d78, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d78, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare475 p hg
    simpa only [d866, d78, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare477 (p : Pattern) (guard : d0 p = 1) : d83 p ≤ (0 : Int) + d232 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare478 (p : Pattern) (guard : d868 p = 1) : d84 p ≤ (0 : Int) + d233 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d84, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare476 p hg
    simpa only [d868, d84, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d84, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare477 p hg
    simpa only [d868, d84, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare479 (p : Pattern) (guard : d868 p = 1) : d85 p ≤ (0 : Int) + d234 p := by
  cases selected : p 106 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d85, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare473 p hg
    simpa only [d85, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d85, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare478 p hg
    simpa only [d85, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare480 (p : Pattern) (guard : d0 p = 1) : d166 p ≤ (0 : Int) + d241 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare481 (p : Pattern) (guard : d869 p = 1) : d174 p ≤ (0 : Int) + d242 p := by
  cases selected : p 86 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d869, d174, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare479 p hg
    simpa only [d869, d174, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d869, d174, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare480 p hg
    simpa only [d869, d174, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare482 (p : Pattern) (guard : d0 p = 1) : d45 p ≤ (0 : Int) + d150 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare483 (p : Pattern) (guard : d866 p = 1) : d45 p ≤ (0 : Int) + d235 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d866, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare482 p hg
    simpa only [d866, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare484 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d243 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare485 (p : Pattern) (guard : d868 p = 1) : d67 p ≤ (0 : Int) + d244 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d67, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare483 p hg
    simpa only [d868, d67, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d67, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare484 p hg
    simpa only [d868, d67, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare486 (p : Pattern) (guard : d0 p = 1) : d77 p ≤ (0 : Int) + d161 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare487 (p : Pattern) (guard : d866 p = 1) : d77 p ≤ (0 : Int) + d238 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare429 p hg
    simpa only [d866, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare486 p hg
    simpa only [d866, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare488 (p : Pattern) (guard : d0 p = 1) : d83 p ≤ (0 : Int) + d245 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare489 (p : Pattern) (guard : d868 p = 1) : d117 p ≤ (0 : Int) + d246 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d868, d117, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare487 p hg
    simpa only [d868, d117, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d868, d117, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare488 p hg
    simpa only [d868, d117, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare490 (p : Pattern) (guard : d868 p = 1) : d118 p ≤ (0 : Int) + d247 p := by
  cases selected : p 106 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d118, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare485 p hg
    simpa only [d118, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d868 p = 1 := by simpa only [d118, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare489 p hg
    simpa only [d118, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare491 (p : Pattern) (guard : d0 p = 1) : d171 p ≤ (0 : Int) + d253 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare492 (p : Pattern) (guard : d869 p = 1) : d175 p ≤ (0 : Int) + d254 p := by
  cases selected : p 86 with
  | false =>
    have hg : d868 p = 1 := by simpa only [d869, d175, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare490 p hg
    simpa only [d869, d175, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d869, d175, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare491 p hg
    simpa only [d869, d175, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare493 (p : Pattern) (guard : d869 p = 1) : d176 p ≤ (0 : Int) + d255 p := by
  cases selected : p 80 with
  | false =>
    have hg : d869 p = 1 := by simpa only [d176, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare481 p hg
    simpa only [d176, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d869 p = 1 := by simpa only [d176, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare492 p hg
    simpa only [d176, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare494 (p : Pattern) (guard : d1 p = 1) : d51 p ≤ (0 : Int) + d51 p := by
  omega
theorem compare495 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare496 (p : Pattern) (guard : d866 p = 1) : d66 p ≤ (0 : Int) + d229 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d66, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare494 p hg
    simpa only [d866, d66, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d66, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare495 p hg
    simpa only [d866, d66, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare497 (p : Pattern) (guard : d866 p = 1) : d67 p ≤ (0 : Int) + d230 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d67, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare471 p hg
    simpa only [d67, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d67, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare496 p hg
    simpa only [d67, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare498 (p : Pattern) (guard : d1 p = 1) : d80 p ≤ (0 : Int) + d80 p := by
  omega
theorem compare499 (p : Pattern) (guard : d0 p = 1) : d82 p ≤ (0 : Int) + d154 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare500 (p : Pattern) (guard : d866 p = 1) : d83 p ≤ (0 : Int) + d232 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d83, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare498 p hg
    simpa only [d866, d83, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d83, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare499 p hg
    simpa only [d866, d83, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare501 (p : Pattern) (guard : d866 p = 1) : d84 p ≤ (0 : Int) + d233 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d84, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare476 p hg
    simpa only [d84, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d84, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d84, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare502 (p : Pattern) (guard : d866 p = 1) : d85 p ≤ (0 : Int) + d234 p := by
  cases selected : p 106 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d85, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare497 p hg
    simpa only [d85, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d85, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare501 p hg
    simpa only [d85, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare503 (p : Pattern) (guard : d0 p = 1) : d95 p ≤ (0 : Int) + d150 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare504 (p : Pattern) (guard : d866 p = 1) : d96 p ≤ (0 : Int) + d235 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d96, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d866, d96, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d96, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare503 p hg
    simpa only [d866, d96, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare505 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d102 p := by
  omega
theorem compare506 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d154 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare507 (p : Pattern) (guard : d866 p = 1) : d102 p ≤ (0 : Int) + d236 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare505 p hg
    simpa only [d866, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare506 p hg
    simpa only [d866, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare508 (p : Pattern) (guard : d866 p = 1) : d103 p ≤ (0 : Int) + d237 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d103, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare504 p hg
    simpa only [d103, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d103, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare507 p hg
    simpa only [d103, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare509 (p : Pattern) (guard : d0 p = 1) : d105 p ≤ (0 : Int) + d161 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare510 (p : Pattern) (guard : d866 p = 1) : d106 p ≤ (0 : Int) + d238 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d106, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare429 p hg
    simpa only [d866, d106, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d106, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare509 p hg
    simpa only [d866, d106, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare511 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (0 : Int) + d108 p := by
  omega
theorem compare512 (p : Pattern) (guard : d0 p = 1) : d112 p ≤ (0 : Int) + d163 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare513 (p : Pattern) (guard : d866 p = 1) : d113 p ≤ (0 : Int) + d239 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d113, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d866, d113, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d113, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare512 p hg
    simpa only [d866, d113, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare514 (p : Pattern) (guard : d866 p = 1) : d114 p ≤ (0 : Int) + d240 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d114, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare510 p hg
    simpa only [d114, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d114, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare513 p hg
    simpa only [d114, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare515 (p : Pattern) (guard : d866 p = 1) : d115 p ≤ (0 : Int) + d241 p := by
  cases selected : p 106 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d115, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare508 p hg
    simpa only [d115, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d115, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare514 p hg
    simpa only [d115, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare516 (p : Pattern) (guard : d866 p = 1) : d116 p ≤ (0 : Int) + d242 p := by
  cases selected : p 86 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d116, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare502 p hg
    simpa only [d116, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d116, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare515 p hg
    simpa only [d116, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare517 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d154 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare518 (p : Pattern) (guard : d866 p = 1) : d66 p ≤ (0 : Int) + d243 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d66, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare494 p hg
    simpa only [d866, d66, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d66, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare517 p hg
    simpa only [d866, d66, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare519 (p : Pattern) (guard : d866 p = 1) : d67 p ≤ (0 : Int) + d244 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d67, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare483 p hg
    simpa only [d67, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d67, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare518 p hg
    simpa only [d67, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare520 (p : Pattern) (guard : d0 p = 1) : d82 p ≤ (0 : Int) + d163 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare521 (p : Pattern) (guard : d866 p = 1) : d83 p ≤ (0 : Int) + d245 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d83, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare498 p hg
    simpa only [d866, d83, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d83, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare520 p hg
    simpa only [d866, d83, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare522 (p : Pattern) (guard : d866 p = 1) : d117 p ≤ (0 : Int) + d246 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d117, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare487 p hg
    simpa only [d117, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d117, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare521 p hg
    simpa only [d117, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare523 (p : Pattern) (guard : d866 p = 1) : d118 p ≤ (0 : Int) + d247 p := by
  cases selected : p 106 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d118, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare519 p hg
    simpa only [d118, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d118, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare522 p hg
    simpa only [d118, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare524 (p : Pattern) (guard : d0 p = 1) : d123 p ≤ (0 : Int) + d161 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare525 (p : Pattern) (guard : d866 p = 1) : d124 p ≤ (0 : Int) + d248 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d124, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d866, d124, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d124, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare524 p hg
    simpa only [d866, d124, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare526 (p : Pattern) (guard : d0 p = 1) : d126 p ≤ (0 : Int) + d163 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare527 (p : Pattern) (guard : d866 p = 1) : d127 p ≤ (0 : Int) + d249 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d127, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare505 p hg
    simpa only [d866, d127, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d127, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare526 p hg
    simpa only [d866, d127, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare528 (p : Pattern) (guard : d866 p = 1) : d128 p ≤ (0 : Int) + d250 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d128, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare525 p hg
    simpa only [d128, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d128, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare527 p hg
    simpa only [d128, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare529 (p : Pattern) (guard : d0 p = 1) : d82 p ≤ (0 : Int) + d167 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare530 (p : Pattern) (guard : d866 p = 1) : d129 p ≤ (0 : Int) + d251 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d866, d129, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare429 p hg
    simpa only [d866, d129, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d866, d129, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare529 p hg
    simpa only [d866, d129, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare531 (p : Pattern) (guard : d866 p = 1) : d130 p ≤ (0 : Int) + d130 p := by
  omega
theorem compare532 (p : Pattern) (guard : d866 p = 1) : d131 p ≤ (0 : Int) + d252 p := by
  cases selected : p 112 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d131, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare530 p hg
    simpa only [d131, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d131, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare531 p hg
    simpa only [d131, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare533 (p : Pattern) (guard : d866 p = 1) : d132 p ≤ (0 : Int) + d253 p := by
  cases selected : p 106 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d132, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare528 p hg
    simpa only [d132, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d132, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare532 p hg
    simpa only [d132, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare534 (p : Pattern) (guard : d866 p = 1) : d133 p ≤ (0 : Int) + d254 p := by
  cases selected : p 86 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d133, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare523 p hg
    simpa only [d133, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d133, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare533 p hg
    simpa only [d133, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare535 (p : Pattern) (guard : d866 p = 1) : d134 p ≤ (0 : Int) + d255 p := by
  cases selected : p 80 with
  | false =>
    have hg : d866 p = 1 := by simpa only [d134, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare516 p hg
    simpa only [d134, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d866 p = 1 := by simpa only [d134, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare534 p hg
    simpa only [d134, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare536 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (0 : Int) + d28 p := by
  omega
theorem compare537 (p : Pattern) (guard : d0 p = 1) : d44 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare538 (p : Pattern) (guard : d841 p = 1) : d45 p ≤ (0 : Int) + d256 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d45, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d841, d45, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d45, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare537 p hg
    simpa only [d841, d45, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare539 (p : Pattern) (guard : d1 p = 1) : d47 p ≤ (0 : Int) + d47 p := by
  omega
theorem compare540 (p : Pattern) (guard : d0 p = 1) : d50 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare541 (p : Pattern) (guard : d841 p = 1) : d51 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d51, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare539 p hg
    simpa only [d841, d51, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d51, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare540 p hg
    simpa only [d841, d51, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare542 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (0 : Int) + d57 p := by
  omega
theorem compare543 (p : Pattern) (guard : d0 p = 1) : d64 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare544 (p : Pattern) (guard : d841 p = 1) : d65 p ≤ (0 : Int) + d258 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d65, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare542 p hg
    simpa only [d841, d65, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d65, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare543 p hg
    simpa only [d841, d65, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare545 (p : Pattern) (guard : d841 p = 1) : d66 p ≤ (0 : Int) + d259 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d66, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare541 p hg
    simpa only [d66, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d66, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare544 p hg
    simpa only [d66, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare546 (p : Pattern) (guard : d841 p = 1) : d67 p ≤ (0 : Int) + d260 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d67, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare538 p hg
    simpa only [d67, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d67, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare545 p hg
    simpa only [d67, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare547 (p : Pattern) (guard : d0 p = 1) : d73 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare548 (p : Pattern) (guard : d841 p = 1) : d74 p ≤ (0 : Int) + d256 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d74, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d841, d74, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d74, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare547 p hg
    simpa only [d841, d74, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare549 (p : Pattern) (guard : d0 p = 1) : d76 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare550 (p : Pattern) (guard : d841 p = 1) : d77 p ≤ (0 : Int) + d261 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d77, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d841, d77, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d77, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare549 p hg
    simpa only [d841, d77, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare551 (p : Pattern) (guard : d841 p = 1) : d78 p ≤ (0 : Int) + d262 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d78, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare548 p hg
    simpa only [d78, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d78, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare550 p hg
    simpa only [d78, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare552 (p : Pattern) (guard : d0 p = 1) : d79 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare553 (p : Pattern) (guard : d841 p = 1) : d80 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d80, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare539 p hg
    simpa only [d841, d80, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d80, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare552 p hg
    simpa only [d841, d80, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare554 (p : Pattern) (guard : d0 p = 1) : d81 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare555 (p : Pattern) (guard : d841 p = 1) : d82 p ≤ (0 : Int) + d263 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d82, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare542 p hg
    simpa only [d841, d82, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d82, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare554 p hg
    simpa only [d841, d82, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare556 (p : Pattern) (guard : d841 p = 1) : d83 p ≤ (0 : Int) + d264 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d83, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare553 p hg
    simpa only [d83, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d83, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare555 p hg
    simpa only [d83, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare557 (p : Pattern) (guard : d841 p = 1) : d84 p ≤ (0 : Int) + d265 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d84, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare551 p hg
    simpa only [d84, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d84, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare556 p hg
    simpa only [d84, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare558 (p : Pattern) (guard : d841 p = 1) : d85 p ≤ (0 : Int) + d266 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d85, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare546 p hg
    simpa only [d85, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d85, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare557 p hg
    simpa only [d85, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare559 (p : Pattern) (guard : d1 p = 1) : d89 p ≤ (0 : Int) + d89 p := by
  omega
end NetHack.Sokoban32Refined
