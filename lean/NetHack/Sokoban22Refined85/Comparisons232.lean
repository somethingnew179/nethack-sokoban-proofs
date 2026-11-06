/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons231
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare32480 (p : Pattern) (guard : d4474 p = 1) : d3104 p ≤ (2 : Int) + d7153 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3104, d7153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32479 p hg
    simpa only [d3104, d7153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3104, d7153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32193 p hg
    simpa only [d3104, d7153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32481 (p : Pattern) (guard : d4474 p = 1) : d3105 p ≤ (2 : Int) + d7154 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3105, d7154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32478 p hg
    simpa only [d3105, d7154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3105, d7154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32480 p hg
    simpa only [d3105, d7154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32482 (p : Pattern) (guard : d4474 p = 1) : d3106 p ≤ (2 : Int) + d7155 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3106, d7155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32458 p hg
    simpa only [d3106, d7155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3106, d7155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32153 p hg
    simpa only [d3106, d7155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32483 (p : Pattern) (guard : d4474 p = 1) : d3107 p ≤ (2 : Int) + d7156 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3107, d7156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32461 p hg
    simpa only [d3107, d7156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3107, d7156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32211 p hg
    simpa only [d3107, d7156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32484 (p : Pattern) (guard : d4474 p = 1) : d3108 p ≤ (2 : Int) + d7157 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3108, d7157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32482 p hg
    simpa only [d3108, d7157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3108, d7157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32483 p hg
    simpa only [d3108, d7157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32485 (p : Pattern) (guard : d4474 p = 1) : d3109 p ≤ (2 : Int) + d7061 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3109, d7061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32461 p hg
    simpa only [d3109, d7061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3109, d7061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3109, d7061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32486 (p : Pattern) (guard : d4474 p = 1) : d3110 p ≤ (2 : Int) + d7062 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3110, d7062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32485 p hg
    simpa only [d3110, d7062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3110, d7062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3110, d7062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32487 (p : Pattern) (guard : d4474 p = 1) : d3111 p ≤ (2 : Int) + d7158 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3111, d7158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32484 p hg
    simpa only [d3111, d7158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3111, d7158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32486 p hg
    simpa only [d3111, d7158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32488 (p : Pattern) (guard : d4474 p = 1) : d3112 p ≤ (2 : Int) + d7159 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3112, d7159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32481 p hg
    simpa only [d3112, d7159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3112, d7159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32487 p hg
    simpa only [d3112, d7159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32489 (p : Pattern) (guard : d4474 p = 1) : d3113 p ≤ (2 : Int) + d7160 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3113, d7160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32467 p hg
    simpa only [d3113, d7160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3113, d7160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32488 p hg
    simpa only [d3113, d7160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32490 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d1778 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15669 p hg
    simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16112 p hg
    simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32491 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d1779 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32490 p hg
    simpa only [d14, d1779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16113 p hg
    simpa only [d14, d1779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32492 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d1780 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32090 p hg
    simpa only [d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32491 p hg
    simpa only [d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32493 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d1781 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32133 p hg
    simpa only [d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32492 p hg
    simpa only [d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32494 (p : Pattern) (guard : d0 p = 1) : d1781 p ≤ (2 : Int) + d1781 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32495 (p : Pattern) (guard : d4474 p = 1) : d3114 p ≤ (2 : Int) + d1781 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32493 p hg
    simpa only [d4474, d3114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32494 p hg
    simpa only [d4474, d3114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32496 (p : Pattern) (guard : d1 p = 1) : d2047 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15813 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15810 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32497 (p : Pattern) (guard : d1 p = 1) : d2048 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15811 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32496 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32498 (p : Pattern) (guard : d4474 p = 1) : d2049 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32497 p hg
    simpa only [d4474, d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32499 (p : Pattern) (guard : d4474 p = 1) : d3115 p ≤ (2 : Int) + d7161 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3115, d7161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32495 p hg
    simpa only [d3115, d7161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3115, d7161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32498 p hg
    simpa only [d3115, d7161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32500 (p : Pattern) (guard : d1 p = 1) : d2051 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15806 p hg
    simpa only [d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1829 p hg
    simpa only [d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32501 (p : Pattern) (guard : d1 p = 1) : d2052 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32500 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32502 (p : Pattern) (guard : d1 p = 1) : d2053 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15813 p hg
    simpa only [d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32501 p hg
    simpa only [d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32503 (p : Pattern) (guard : d1 p = 1) : d2054 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15811 p hg
    simpa only [d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32502 p hg
    simpa only [d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32504 (p : Pattern) (guard : d4474 p = 1) : d2055 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32503 p hg
    simpa only [d4474, d2055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d2055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32505 (p : Pattern) (guard : d4474 p = 1) : d3116 p ≤ (2 : Int) + d7022 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3116, d7022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d3116, d7022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3116, d7022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32504 p hg
    simpa only [d3116, d7022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32506 (p : Pattern) (guard : d4474 p = 1) : d3117 p ≤ (2 : Int) + d7162 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3117, d7162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32499 p hg
    simpa only [d3117, d7162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3117, d7162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32505 p hg
    simpa only [d3117, d7162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32507 (p : Pattern) (guard : d4474 p = 1) : d3118 p ≤ (2 : Int) + d7163 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3118, d7163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32506 p hg
    simpa only [d3118, d7163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3118, d7163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32258 p hg
    simpa only [d3118, d7163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32508 (p : Pattern) (guard : d4474 p = 1) : d3119 p ≤ (2 : Int) + d7164 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3119, d7164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32507 p hg
    simpa only [d3119, d7164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3119, d7164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32259 p hg
    simpa only [d3119, d7164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32509 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (2 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16154 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12275 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32510 (p : Pattern) (guard : d1 p = 1) : d191 p ≤ (2 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d191, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32509 p hg
    simpa only [d191, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d191, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12276 p hg
    simpa only [d191, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32511 (p : Pattern) (guard : d1 p = 1) : d191 p ≤ (2 : Int) + d2060 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13406 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32510 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32512 (p : Pattern) (guard : d1 p = 1) : d191 p ≤ (2 : Int) + d2061 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32511 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32510 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32513 (p : Pattern) (guard : d0 p = 1) : d2061 p ≤ (2 : Int) + d2061 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32514 (p : Pattern) (guard : d4474 p = 1) : d3120 p ≤ (2 : Int) + d2061 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32512 p hg
    simpa only [d4474, d3120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32513 p hg
    simpa only [d4474, d3120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32515 (p : Pattern) (guard : d1 p = 1) : d315 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12276 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32516 (p : Pattern) (guard : d1 p = 1) : d2060 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12277 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32515 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32517 (p : Pattern) (guard : d1 p = 1) : d2061 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32516 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32515 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32518 (p : Pattern) (guard : d4474 p = 1) : d2062 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32517 p hg
    simpa only [d4474, d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32519 (p : Pattern) (guard : d4474 p = 1) : d3121 p ≤ (2 : Int) + d7165 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3121, d7165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32514 p hg
    simpa only [d3121, d7165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3121, d7165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32518 p hg
    simpa only [d3121, d7165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32520 (p : Pattern) (guard : d4474 p = 1) : d3122 p ≤ (2 : Int) + d7166 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3122, d7166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32240 p hg
    simpa only [d3122, d7166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3122, d7166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32519 p hg
    simpa only [d3122, d7166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32521 (p : Pattern) (guard : d4474 p = 1) : d3123 p ≤ (2 : Int) + d7167 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3123, d7167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32520 p hg
    simpa only [d3123, d7167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3123, d7167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3123, d7167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32522 (p : Pattern) (guard : d4474 p = 1) : d3124 p ≤ (2 : Int) + d7168 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3124, d7168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32521 p hg
    simpa only [d3124, d7168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3124, d7168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3124, d7168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32523 (p : Pattern) (guard : d4474 p = 1) : d3125 p ≤ (2 : Int) + d7169 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3125, d7169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32508 p hg
    simpa only [d3125, d7169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3125, d7169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32522 p hg
    simpa only [d3125, d7169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32524 (p : Pattern) (guard : d1 p = 1) : d2068 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12151 p hg
    simpa only [d2068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1829 p hg
    simpa only [d2068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32525 (p : Pattern) (guard : d1 p = 1) : d2069 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32524 p hg
    simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32526 (p : Pattern) (guard : d1 p = 1) : d2070 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15837 p hg
    simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32525 p hg
    simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32527 (p : Pattern) (guard : d1 p = 1) : d2071 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15835 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32526 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32528 (p : Pattern) (guard : d4474 p = 1) : d2072 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32527 p hg
    simpa only [d4474, d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32529 (p : Pattern) (guard : d4474 p = 1) : d3126 p ≤ (2 : Int) + d7039 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3126, d7039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32204 p hg
    simpa only [d3126, d7039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3126, d7039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32528 p hg
    simpa only [d3126, d7039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32530 (p : Pattern) (guard : d4474 p = 1) : d3127 p ≤ (2 : Int) + d7039 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32529 p hg
    simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32247 p hg
    simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32531 (p : Pattern) (guard : d4474 p = 1) : d3128 p ≤ (2 : Int) + d7170 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3128, d7170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32240 p hg
    simpa only [d3128, d7170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3128, d7170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32192 p hg
    simpa only [d3128, d7170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32532 (p : Pattern) (guard : d4474 p = 1) : d3129 p ≤ (2 : Int) + d7171 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3129, d7171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32530 p hg
    simpa only [d3129, d7171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3129, d7171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32531 p hg
    simpa only [d3129, d7171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32533 (p : Pattern) (guard : d4474 p = 1) : d3130 p ≤ (2 : Int) + d7172 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3130, d7172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32532 p hg
    simpa only [d3130, d7172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3130, d7172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32269 p hg
    simpa only [d3130, d7172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32534 (p : Pattern) (guard : d4474 p = 1) : d3131 p ≤ (2 : Int) + d7173 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3131, d7173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32519 p hg
    simpa only [d3131, d7173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3131, d7173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3131, d7173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32535 (p : Pattern) (guard : d4474 p = 1) : d3132 p ≤ (2 : Int) + d7174 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3132, d7174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32534 p hg
    simpa only [d3132, d7174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3132, d7174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3132, d7174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32536 (p : Pattern) (guard : d4474 p = 1) : d3133 p ≤ (2 : Int) + d7175 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3133, d7175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32535 p hg
    simpa only [d3133, d7175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3133, d7175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3133, d7175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32537 (p : Pattern) (guard : d4474 p = 1) : d3134 p ≤ (2 : Int) + d7176 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3134, d7176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32533 p hg
    simpa only [d3134, d7176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3134, d7176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32536 p hg
    simpa only [d3134, d7176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32538 (p : Pattern) (guard : d4474 p = 1) : d3135 p ≤ (2 : Int) + d7177 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3135, d7177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32523 p hg
    simpa only [d3135, d7177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3135, d7177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32537 p hg
    simpa only [d3135, d7177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32539 (p : Pattern) (guard : d4474 p = 1) : d3136 p ≤ (2 : Int) + d7178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3136, d7178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32489 p hg
    simpa only [d3136, d7178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3136, d7178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32538 p hg
    simpa only [d3136, d7178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32540 (p : Pattern) (guard : d4474 p = 1) : d3137 p ≤ (2 : Int) + d7179 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3137, d7179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32538 p hg
    simpa only [d3137, d7179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3137, d7179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3137, d7179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32541 (p : Pattern) (guard : d4474 p = 1) : d3138 p ≤ (2 : Int) + d7180 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3138, d7180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32539 p hg
    simpa only [d3138, d7180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3138, d7180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32540 p hg
    simpa only [d3138, d7180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32542 (p : Pattern) (guard : d4474 p = 1) : d3139 p ≤ (2 : Int) + d7181 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3139, d7181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32283 p hg
    simpa only [d3139, d7181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3139, d7181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32541 p hg
    simpa only [d3139, d7181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32543 (p : Pattern) (guard : d4474 p = 1) : d3140 p ≤ (2 : Int) + d7182 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3140, d7182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32286 p hg
    simpa only [d3140, d7182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3140, d7182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32542 p hg
    simpa only [d3140, d7182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32544 (p : Pattern) (guard : d4474 p = 1) : d3141 p ≤ (2 : Int) + d7183 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3141, d7183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32310 p hg
    simpa only [d3141, d7183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3141, d7183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3141, d7183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32545 (p : Pattern) (guard : d4474 p = 1) : d3142 p ≤ (2 : Int) + d7184 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3142, d7184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32357 p hg
    simpa only [d3142, d7184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3142, d7184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32544 p hg
    simpa only [d3142, d7184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32546 (p : Pattern) (guard : d4474 p = 1) : d3143 p ≤ (2 : Int) + d7185 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3143, d7185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32544 p hg
    simpa only [d3143, d7185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3143, d7185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3143, d7185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32547 (p : Pattern) (guard : d4474 p = 1) : d3144 p ≤ (2 : Int) + d7186 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3144, d7186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32545 p hg
    simpa only [d3144, d7186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3144, d7186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32546 p hg
    simpa only [d3144, d7186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32548 (p : Pattern) (guard : d4474 p = 1) : d3145 p ≤ (2 : Int) + d7187 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3145, d7187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32338 p hg
    simpa only [d3145, d7187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3145, d7187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3145, d7187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32549 (p : Pattern) (guard : d4474 p = 1) : d3146 p ≤ (2 : Int) + d7188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3146, d7188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32373 p hg
    simpa only [d3146, d7188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3146, d7188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32548 p hg
    simpa only [d3146, d7188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32550 (p : Pattern) (guard : d4474 p = 1) : d3147 p ≤ (2 : Int) + d7189 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3147, d7189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32548 p hg
    simpa only [d3147, d7189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3147, d7189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3147, d7189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32551 (p : Pattern) (guard : d4474 p = 1) : d3148 p ≤ (2 : Int) + d7190 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3148, d7190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32549 p hg
    simpa only [d3148, d7190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3148, d7190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32550 p hg
    simpa only [d3148, d7190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32552 (p : Pattern) (guard : d4474 p = 1) : d3149 p ≤ (2 : Int) + d7191 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3149, d7191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32547 p hg
    simpa only [d3149, d7191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3149, d7191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32551 p hg
    simpa only [d3149, d7191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32553 (p : Pattern) (guard : d4474 p = 1) : d3150 p ≤ (2 : Int) + d7192 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3150, d7192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32344 p hg
    simpa only [d3150, d7192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3150, d7192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32552 p hg
    simpa only [d3150, d7192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32554 (p : Pattern) (guard : d4474 p = 1) : d3151 p ≤ (2 : Int) + d7187 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3151, d7187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32403 p hg
    simpa only [d3151, d7187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3151, d7187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3151, d7187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32555 (p : Pattern) (guard : d4474 p = 1) : d3152 p ≤ (2 : Int) + d7193 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3152, d7193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32423 p hg
    simpa only [d3152, d7193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3152, d7193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32554 p hg
    simpa only [d3152, d7193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32556 (p : Pattern) (guard : d4474 p = 1) : d3153 p ≤ (2 : Int) + d7189 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3153, d7189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32554 p hg
    simpa only [d3153, d7189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3153, d7189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3153, d7189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32557 (p : Pattern) (guard : d4474 p = 1) : d3154 p ≤ (2 : Int) + d7194 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3154, d7194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32555 p hg
    simpa only [d3154, d7194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3154, d7194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32556 p hg
    simpa only [d3154, d7194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32558 (p : Pattern) (guard : d4474 p = 1) : d3155 p ≤ (2 : Int) + d7195 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3155, d7195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32557 p hg
    simpa only [d3155, d7195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3155, d7195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32431 p hg
    simpa only [d3155, d7195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32559 (p : Pattern) (guard : d4474 p = 1) : d3156 p ≤ (2 : Int) + d7196 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3156, d7196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32422 p hg
    simpa only [d3156, d7196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3156, d7196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32558 p hg
    simpa only [d3156, d7196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32560 (p : Pattern) (guard : d4474 p = 1) : d3157 p ≤ (2 : Int) + d7197 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3157, d7197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32553 p hg
    simpa only [d3157, d7197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3157, d7197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32559 p hg
    simpa only [d3157, d7197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32561 (p : Pattern) (guard : d4474 p = 1) : d3158 p ≤ (2 : Int) + d7198 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3158, d7198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32559 p hg
    simpa only [d3158, d7198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3158, d7198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32438 p hg
    simpa only [d3158, d7198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32562 (p : Pattern) (guard : d4474 p = 1) : d3159 p ≤ (2 : Int) + d7199 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3159, d7199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32560 p hg
    simpa only [d3159, d7199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3159, d7199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32561 p hg
    simpa only [d3159, d7199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32563 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d9 p := by
  change (1 : Int) ≤ (2 : Int) + 9
  decide
theorem compare32564 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d1948 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15921 p hg
    simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32563 p hg
    simpa only [d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32565 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (2 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32563 p hg
    simpa only [d102, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d102, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32566 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d1949 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32564 p hg
    simpa only [d103, d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32565 p hg
    simpa only [d103, d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32567 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d1950 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32288 p hg
    simpa only [d1950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32566 p hg
    simpa only [d1950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32568 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d1951 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32318 p hg
    simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32567 p hg
    simpa only [d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32569 (p : Pattern) (guard : d0 p = 1) : d1951 p ≤ (2 : Int) + d1951 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32570 (p : Pattern) (guard : d4474 p = 1) : d3160 p ≤ (2 : Int) + d1951 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32568 p hg
    simpa only [d4474, d3160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32569 p hg
    simpa only [d4474, d3160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32571 (p : Pattern) (guard : d1 p = 1) : d2107 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16004 p hg
    simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16001 p hg
    simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32572 (p : Pattern) (guard : d1 p = 1) : d2108 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16002 p hg
    simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32571 p hg
    simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32573 (p : Pattern) (guard : d4474 p = 1) : d2109 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32572 p hg
    simpa only [d4474, d2109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d2109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32574 (p : Pattern) (guard : d4474 p = 1) : d3161 p ≤ (2 : Int) + d7200 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3161, d7200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32570 p hg
    simpa only [d3161, d7200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3161, d7200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32573 p hg
    simpa only [d3161, d7200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32575 (p : Pattern) (guard : d4474 p = 1) : d3162 p ≤ (2 : Int) + d7201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3162, d7201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32574 p hg
    simpa only [d3162, d7201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3162, d7201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32403 p hg
    simpa only [d3162, d7201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32576 (p : Pattern) (guard : d4474 p = 1) : d3163 p ≤ (2 : Int) + d7202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3163, d7202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32388 p hg
    simpa only [d3163, d7202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3163, d7202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32575 p hg
    simpa only [d3163, d7202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32577 (p : Pattern) (guard : d4474 p = 1) : d3164 p ≤ (2 : Int) + d7203 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3164, d7203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32400 p hg
    simpa only [d3164, d7203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3164, d7203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32403 p hg
    simpa only [d3164, d7203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32578 (p : Pattern) (guard : d4474 p = 1) : d3165 p ≤ (2 : Int) + d7204 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3165, d7204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32577 p hg
    simpa only [d3165, d7204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3165, d7204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32313 p hg
    simpa only [d3165, d7204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32579 (p : Pattern) (guard : d4474 p = 1) : d3166 p ≤ (2 : Int) + d7205 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3166, d7205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32576 p hg
    simpa only [d3166, d7205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3166, d7205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32578 p hg
    simpa only [d3166, d7205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32580 (p : Pattern) (guard : d4474 p = 1) : d3167 p ≤ (2 : Int) + d7101 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3167, d7101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32371 p hg
    simpa only [d3167, d7101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3167, d7101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16285 p hg
    simpa only [d3167, d7101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32581 (p : Pattern) (guard : d4474 p = 1) : d3168 p ≤ (2 : Int) + d7101 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32408 p hg
    simpa only [d3168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32580 p hg
    simpa only [d3168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32582 (p : Pattern) (guard : d4474 p = 1) : d3169 p ≤ (2 : Int) + d7206 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3169, d7206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32581 p hg
    simpa only [d3169, d7206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3169, d7206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32548 p hg
    simpa only [d3169, d7206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32583 (p : Pattern) (guard : d4474 p = 1) : d3170 p ≤ (2 : Int) + d7115 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3170, d7115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32417 p hg
    simpa only [d3170, d7115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3170, d7115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3170, d7115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32584 (p : Pattern) (guard : d4474 p = 1) : d3171 p ≤ (2 : Int) + d7123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3171, d7123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32583 p hg
    simpa only [d3171, d7123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3171, d7123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3171, d7123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32585 (p : Pattern) (guard : d4474 p = 1) : d3172 p ≤ (2 : Int) + d7124 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3172, d7124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32584 p hg
    simpa only [d3172, d7124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3172, d7124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3172, d7124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32586 (p : Pattern) (guard : d4474 p = 1) : d3173 p ≤ (2 : Int) + d7207 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3173, d7207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32582 p hg
    simpa only [d3173, d7207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3173, d7207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32585 p hg
    simpa only [d3173, d7207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32587 (p : Pattern) (guard : d4474 p = 1) : d3174 p ≤ (2 : Int) + d7208 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3174, d7208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32579 p hg
    simpa only [d3174, d7208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3174, d7208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32586 p hg
    simpa only [d3174, d7208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32588 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d3175 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32346 p hg
    simpa only [d3175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32364 p hg
    simpa only [d3175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32589 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d3176 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32365 p hg
    simpa only [d3176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32588 p hg
    simpa only [d3176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32590 (p : Pattern) (guard : d0 p = 1) : d3176 p ≤ (2 : Int) + d3176 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32591 (p : Pattern) (guard : d4474 p = 1) : d3177 p ≤ (2 : Int) + d3176 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32589 p hg
    simpa only [d4474, d3177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32590 p hg
    simpa only [d4474, d3177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32592 (p : Pattern) (guard : d1 p = 1) : d2124 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16033 p hg
    simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32593 (p : Pattern) (guard : d1 p = 1) : d2125 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32592 p hg
    simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16033 p hg
    simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32594 (p : Pattern) (guard : d4474 p = 1) : d2126 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32593 p hg
    simpa only [d4474, d2126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d2126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32595 (p : Pattern) (guard : d4474 p = 1) : d3178 p ≤ (2 : Int) + d7209 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3178, d7209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32591 p hg
    simpa only [d3178, d7209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3178, d7209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32594 p hg
    simpa only [d3178, d7209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32596 (p : Pattern) (guard : d4474 p = 1) : d3179 p ≤ (2 : Int) + d7210 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3179, d7210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32574 p hg
    simpa only [d3179, d7210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3179, d7210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32595 p hg
    simpa only [d3179, d7210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32597 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d2135 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32300 p hg
    simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32330 p hg
    simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32598 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d2136 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32331 p hg
    simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32597 p hg
    simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32599 (p : Pattern) (guard : d0 p = 1) : d2136 p ≤ (2 : Int) + d2136 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32600 (p : Pattern) (guard : d4474 p = 1) : d3180 p ≤ (2 : Int) + d2136 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32598 p hg
    simpa only [d4474, d3180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32599 p hg
    simpa only [d4474, d3180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32601 (p : Pattern) (guard : d1 p = 1) : d2129 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4787 p hg
    simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16015 p hg
    simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32602 (p : Pattern) (guard : d1 p = 1) : d2130 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32601 p hg
    simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16015 p hg
    simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32603 (p : Pattern) (guard : d4474 p = 1) : d2131 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32602 p hg
    simpa only [d4474, d2131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d2131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32604 (p : Pattern) (guard : d4474 p = 1) : d3181 p ≤ (2 : Int) + d7211 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3181, d7211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32600 p hg
    simpa only [d3181, d7211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3181, d7211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32603 p hg
    simpa only [d3181, d7211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32605 (p : Pattern) (guard : d4474 p = 1) : d3182 p ≤ (2 : Int) + d7212 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3182, d7212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32604 p hg
    simpa only [d3182, d7212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3182, d7212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3182, d7212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32606 (p : Pattern) (guard : d4474 p = 1) : d3183 p ≤ (2 : Int) + d7213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3183, d7213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32596 p hg
    simpa only [d3183, d7213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3183, d7213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32605 p hg
    simpa only [d3183, d7213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32607 (p : Pattern) (guard : d1 p = 1) : d2135 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16015 p hg
    simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16012 p hg
    simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32608 (p : Pattern) (guard : d1 p = 1) : d2136 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16013 p hg
    simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32607 p hg
    simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32609 (p : Pattern) (guard : d4474 p = 1) : d2137 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32608 p hg
    simpa only [d4474, d2137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d2137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32610 (p : Pattern) (guard : d4474 p = 1) : d3184 p ≤ (2 : Int) + d7088 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3184, d7088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32337 p hg
    simpa only [d3184, d7088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3184, d7088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32609 p hg
    simpa only [d3184, d7088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32611 (p : Pattern) (guard : d4474 p = 1) : d3185 p ≤ (2 : Int) + d7187 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3185, d7187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32610 p hg
    simpa only [d3185, d7187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3185, d7187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3185, d7187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32612 (p : Pattern) (guard : d4474 p = 1) : d3186 p ≤ (2 : Int) + d7189 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3186, d7189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32611 p hg
    simpa only [d3186, d7189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3186, d7189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3186, d7189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32613 (p : Pattern) (guard : d4474 p = 1) : d3187 p ≤ (2 : Int) + d7214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3187, d7214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32606 p hg
    simpa only [d3187, d7214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3187, d7214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32612 p hg
    simpa only [d3187, d7214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32614 (p : Pattern) (guard : d4474 p = 1) : d3188 p ≤ (2 : Int) + d7088 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3188, d7088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32337 p hg
    simpa only [d3188, d7088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3188, d7088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16285 p hg
    simpa only [d3188, d7088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32615 (p : Pattern) (guard : d4474 p = 1) : d3189 p ≤ (2 : Int) + d7088 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32614 p hg
    simpa only [d3189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32338 p hg
    simpa only [d3189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32616 (p : Pattern) (guard : d4474 p = 1) : d3190 p ≤ (2 : Int) + d7215 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3190, d7215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32615 p hg
    simpa only [d3190, d7215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3190, d7215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32584 p hg
    simpa only [d3190, d7215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32617 (p : Pattern) (guard : d4474 p = 1) : d3191 p ≤ (2 : Int) + d7216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3191, d7216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32159 p hg
    simpa only [d3191, d7216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3191, d7216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3191, d7216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32618 (p : Pattern) (guard : d4474 p = 1) : d3192 p ≤ (2 : Int) + d7217 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3192, d7217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32616 p hg
    simpa only [d3192, d7217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3192, d7217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32617 p hg
    simpa only [d3192, d7217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32619 (p : Pattern) (guard : d4474 p = 1) : d3193 p ≤ (2 : Int) + d7218 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3193, d7218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32613 p hg
    simpa only [d3193, d7218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3193, d7218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32618 p hg
    simpa only [d3193, d7218, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
