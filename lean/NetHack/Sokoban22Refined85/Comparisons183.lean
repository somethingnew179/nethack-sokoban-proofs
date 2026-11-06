/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons182
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare25620 (p : Pattern) (guard : d5540 p = 1) : d3048 p ≤ (2 : Int) + d6195 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3048, d6195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25589 p hg
    simpa only [d3048, d6195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3048, d6195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25548 p hg
    simpa only [d3048, d6195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25621 (p : Pattern) (guard : d5540 p = 1) : d120 p ≤ (2 : Int) + d120 p := by
  omega
theorem compare25622 (p : Pattern) (guard : d5540 p = 1) : d3049 p ≤ (2 : Int) + d6196 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3049, d6196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25621 p hg
    simpa only [d3049, d6196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3049, d6196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25555 p hg
    simpa only [d3049, d6196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25623 (p : Pattern) (guard : d5540 p = 1) : d3050 p ≤ (2 : Int) + d6197 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3050, d6197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25622 p hg
    simpa only [d3050, d6197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3050, d6197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25556 p hg
    simpa only [d3050, d6197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25624 (p : Pattern) (guard : d5540 p = 1) : d3051 p ≤ (2 : Int) + d6198 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3051, d6198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25620 p hg
    simpa only [d3051, d6198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3051, d6198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25623 p hg
    simpa only [d3051, d6198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25625 (p : Pattern) (guard : d5540 p = 1) : d3052 p ≤ (2 : Int) + d6199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3052, d6199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25624 p hg
    simpa only [d3052, d6199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3052, d6199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3052, d6199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25626 (p : Pattern) (guard : d5540 p = 1) : d3053 p ≤ (2 : Int) + d6200 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3053, d6200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25625 p hg
    simpa only [d3053, d6200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3053, d6200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3053, d6200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25627 (p : Pattern) (guard : d5540 p = 1) : d3054 p ≤ (2 : Int) + d6201 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3054, d6201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25619 p hg
    simpa only [d3054, d6201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3054, d6201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25626 p hg
    simpa only [d3054, d6201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25628 (p : Pattern) (guard : d5540 p = 1) : d3055 p ≤ (2 : Int) + d6202 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3055, d6202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25610 p hg
    simpa only [d3055, d6202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3055, d6202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25620 p hg
    simpa only [d3055, d6202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25629 (p : Pattern) (guard : d5540 p = 1) : d3056 p ≤ (2 : Int) + d6203 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3056, d6203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25615 p hg
    simpa only [d3056, d6203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3056, d6203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25431 p hg
    simpa only [d3056, d6203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25630 (p : Pattern) (guard : d5540 p = 1) : d3057 p ≤ (2 : Int) + d6204 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3057, d6204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25628 p hg
    simpa only [d3057, d6204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3057, d6204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25629 p hg
    simpa only [d3057, d6204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25631 (p : Pattern) (guard : d5540 p = 1) : d3058 p ≤ (2 : Int) + d6205 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3058, d6205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25615 p hg
    simpa only [d3058, d6205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3058, d6205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25435 p hg
    simpa only [d3058, d6205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25632 (p : Pattern) (guard : d5540 p = 1) : d3059 p ≤ (2 : Int) + d6206 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3059, d6206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25631 p hg
    simpa only [d3059, d6206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3059, d6206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3059, d6206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25633 (p : Pattern) (guard : d5540 p = 1) : d3060 p ≤ (2 : Int) + d6207 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3060, d6207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25630 p hg
    simpa only [d3060, d6207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3060, d6207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25632 p hg
    simpa only [d3060, d6207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25634 (p : Pattern) (guard : d5540 p = 1) : d3061 p ≤ (2 : Int) + d6208 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3061, d6208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25623 p hg
    simpa only [d3061, d6208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3061, d6208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3061, d6208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25635 (p : Pattern) (guard : d5540 p = 1) : d3062 p ≤ (2 : Int) + d6209 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3062, d6209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25634 p hg
    simpa only [d3062, d6209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3062, d6209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3062, d6209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25636 (p : Pattern) (guard : d5540 p = 1) : d3063 p ≤ (2 : Int) + d6210 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3063, d6210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25635 p hg
    simpa only [d3063, d6210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3063, d6210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3063, d6210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25637 (p : Pattern) (guard : d5540 p = 1) : d3064 p ≤ (2 : Int) + d6211 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3064, d6211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25633 p hg
    simpa only [d3064, d6211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3064, d6211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25636 p hg
    simpa only [d3064, d6211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25638 (p : Pattern) (guard : d5540 p = 1) : d3065 p ≤ (2 : Int) + d6212 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3065, d6212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25627 p hg
    simpa only [d3065, d6212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3065, d6212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25637 p hg
    simpa only [d3065, d6212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25639 (p : Pattern) (guard : d5540 p = 1) : d3066 p ≤ (2 : Int) + d6213 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3066, d6213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25598 p hg
    simpa only [d3066, d6213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3066, d6213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25638 p hg
    simpa only [d3066, d6213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25640 (p : Pattern) (guard : d5540 p = 1) : d3067 p ≤ (2 : Int) + d6214 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3067, d6214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25537 p hg
    simpa only [d3067, d6214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3067, d6214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3067, d6214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25641 (p : Pattern) (guard : d5540 p = 1) : d3068 p ≤ (2 : Int) + d6215 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3068, d6215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25640 p hg
    simpa only [d3068, d6215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3068, d6215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3068, d6215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25642 (p : Pattern) (guard : d5540 p = 1) : d3069 p ≤ (2 : Int) + d6216 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3069, d6216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25641 p hg
    simpa only [d3069, d6216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3069, d6216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3069, d6216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25643 (p : Pattern) (guard : d5540 p = 1) : d3070 p ≤ (2 : Int) + d6217 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3070, d6217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25642 p hg
    simpa only [d3070, d6217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3070, d6217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3070, d6217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25644 (p : Pattern) (guard : d5540 p = 1) : d3071 p ≤ (2 : Int) + d6218 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3071, d6218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25638 p hg
    simpa only [d3071, d6218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3071, d6218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25643 p hg
    simpa only [d3071, d6218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25645 (p : Pattern) (guard : d5540 p = 1) : d3072 p ≤ (2 : Int) + d6219 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3072, d6219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25639 p hg
    simpa only [d3072, d6219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3072, d6219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25644 p hg
    simpa only [d3072, d6219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25646 (p : Pattern) (guard : d5540 p = 1) : d3073 p ≤ (2 : Int) + d6220 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3073, d6220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25638 p hg
    simpa only [d3073, d6220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3073, d6220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3073, d6220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25647 (p : Pattern) (guard : d5540 p = 1) : d3074 p ≤ (2 : Int) + d6221 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3074, d6221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25639 p hg
    simpa only [d3074, d6221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3074, d6221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25646 p hg
    simpa only [d3074, d6221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25648 (p : Pattern) (guard : d5540 p = 1) : d3075 p ≤ (2 : Int) + d6222 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3075, d6222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25645 p hg
    simpa only [d3075, d6222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3075, d6222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25647 p hg
    simpa only [d3075, d6222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25649 (p : Pattern) (guard : d5540 p = 1) : d3076 p ≤ (2 : Int) + d6223 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3076, d6223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d3076, d6223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3076, d6223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25648 p hg
    simpa only [d3076, d6223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25650 (p : Pattern) (guard : d5540 p = 1) : d3077 p ≤ (2 : Int) + d6224 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3077, d6224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d3077, d6224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3077, d6224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25649 p hg
    simpa only [d3077, d6224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25651 (p : Pattern) (guard : d0 p = 1) : d3078 p ≤ (2 : Int) + d1795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25652 (p : Pattern) (guard : d5540 p = 1) : d3079 p ≤ (2 : Int) + d1795 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d3079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25394 p hg
    simpa only [d5540, d3079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d3079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25651 p hg
    simpa only [d5540, d3079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25653 (p : Pattern) (guard : d5540 p = 1) : d3080 p ≤ (2 : Int) + d6047 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3080, d6047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25336 p hg
    simpa only [d3080, d6047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3080, d6047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25652 p hg
    simpa only [d3080, d6047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25654 (p : Pattern) (guard : d5540 p = 1) : d2013 p ≤ (2 : Int) + d6104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2013, d6104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25340 p hg
    simpa only [d2013, d6104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2013, d6104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2013, d6104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25655 (p : Pattern) (guard : d5540 p = 1) : d3081 p ≤ (2 : Int) + d6105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3081, d6105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25653 p hg
    simpa only [d3081, d6105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3081, d6105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25654 p hg
    simpa only [d3081, d6105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25656 (p : Pattern) (guard : d5540 p = 1) : d3082 p ≤ (2 : Int) + d6106 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3082, d6106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d3082, d6106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3082, d6106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25655 p hg
    simpa only [d3082, d6106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25657 (p : Pattern) (guard : d5540 p = 1) : d3083 p ≤ (2 : Int) + d6107 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3083, d6107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d3083, d6107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3083, d6107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25656 p hg
    simpa only [d3083, d6107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25658 (p : Pattern) (guard : d5540 p = 1) : d3084 p ≤ (2 : Int) + d6111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3084, d6111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25656 p hg
    simpa only [d3084, d6111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3084, d6111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25473 p hg
    simpa only [d3084, d6111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25659 (p : Pattern) (guard : d5540 p = 1) : d3085 p ≤ (2 : Int) + d6112 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3085, d6112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25657 p hg
    simpa only [d3085, d6112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3085, d6112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25658 p hg
    simpa only [d3085, d6112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25660 (p : Pattern) (guard : d5540 p = 1) : d3086 p ≤ (2 : Int) + d6225 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3086, d6225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25439 p hg
    simpa only [d3086, d6225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3086, d6225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25384 p hg
    simpa only [d3086, d6225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25661 (p : Pattern) (guard : d5540 p = 1) : d3087 p ≤ (2 : Int) + d6226 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3087, d6226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d3087, d6226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3087, d6226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25660 p hg
    simpa only [d3087, d6226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25662 (p : Pattern) (guard : d5540 p = 1) : d3088 p ≤ (2 : Int) + d6227 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3088, d6227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25439 p hg
    simpa only [d3088, d6227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3088, d6227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25392 p hg
    simpa only [d3088, d6227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25663 (p : Pattern) (guard : d5540 p = 1) : d3089 p ≤ (2 : Int) + d6228 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3089, d6228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25478 p hg
    simpa only [d3089, d6228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3089, d6228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3089, d6228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25664 (p : Pattern) (guard : d5540 p = 1) : d3090 p ≤ (2 : Int) + d6229 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3090, d6229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25662 p hg
    simpa only [d3090, d6229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3090, d6229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25663 p hg
    simpa only [d3090, d6229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25665 (p : Pattern) (guard : d5540 p = 1) : d3091 p ≤ (2 : Int) + d6230 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3091, d6230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25661 p hg
    simpa only [d3091, d6230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3091, d6230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25664 p hg
    simpa only [d3091, d6230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25666 (p : Pattern) (guard : d5540 p = 1) : d3092 p ≤ (2 : Int) + d6231 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3092, d6231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25440 p hg
    simpa only [d3092, d6231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3092, d6231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25663 p hg
    simpa only [d3092, d6231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25667 (p : Pattern) (guard : d5540 p = 1) : d3093 p ≤ (2 : Int) + d6232 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3093, d6232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25666 p hg
    simpa only [d3093, d6232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3093, d6232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25447 p hg
    simpa only [d3093, d6232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25668 (p : Pattern) (guard : d5540 p = 1) : d3094 p ≤ (2 : Int) + d6233 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3094, d6233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25665 p hg
    simpa only [d3094, d6233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3094, d6233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25667 p hg
    simpa only [d3094, d6233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25669 (p : Pattern) (guard : d5540 p = 1) : d3095 p ≤ (2 : Int) + d6234 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3095, d6234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25659 p hg
    simpa only [d3095, d6234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3095, d6234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25668 p hg
    simpa only [d3095, d6234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25670 (p : Pattern) (guard : d0 p = 1) : d3096 p ≤ (2 : Int) + d1714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25671 (p : Pattern) (guard : d5540 p = 1) : d3097 p ≤ (2 : Int) + d1714 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d3097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25373 p hg
    simpa only [d5540, d3097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d3097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25670 p hg
    simpa only [d5540, d3097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25672 (p : Pattern) (guard : d5540 p = 1) : d3098 p ≤ (2 : Int) + d6075 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3098, d6075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25408 p hg
    simpa only [d3098, d6075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3098, d6075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25671 p hg
    simpa only [d3098, d6075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25673 (p : Pattern) (guard : d5540 p = 1) : d2031 p ≤ (2 : Int) + d6058 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2031, d6058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25411 p hg
    simpa only [d2031, d6058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2031, d6058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2031, d6058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25674 (p : Pattern) (guard : d5540 p = 1) : d3099 p ≤ (2 : Int) + d6113 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3099, d6113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25672 p hg
    simpa only [d3099, d6113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3099, d6113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25673 p hg
    simpa only [d3099, d6113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25675 (p : Pattern) (guard : d5540 p = 1) : d3100 p ≤ (2 : Int) + d6120 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3100, d6120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d3100, d6120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3100, d6120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25674 p hg
    simpa only [d3100, d6120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25676 (p : Pattern) (guard : d5540 p = 1) : d3101 p ≤ (2 : Int) + d6121 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3101, d6121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25655 p hg
    simpa only [d3101, d6121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3101, d6121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25472 p hg
    simpa only [d3101, d6121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25677 (p : Pattern) (guard : d5540 p = 1) : d3102 p ≤ (2 : Int) + d6122 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3102, d6122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25675 p hg
    simpa only [d3102, d6122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3102, d6122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25676 p hg
    simpa only [d3102, d6122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25678 (p : Pattern) (guard : d5540 p = 1) : d3103 p ≤ (2 : Int) + d6123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3103, d6123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25655 p hg
    simpa only [d3103, d6123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3103, d6123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25431 p hg
    simpa only [d3103, d6123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25679 (p : Pattern) (guard : d5540 p = 1) : d3104 p ≤ (2 : Int) + d6124 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3104, d6124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25678 p hg
    simpa only [d3104, d6124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3104, d6124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25436 p hg
    simpa only [d3104, d6124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25680 (p : Pattern) (guard : d5540 p = 1) : d3105 p ≤ (2 : Int) + d6125 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3105, d6125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25677 p hg
    simpa only [d3105, d6125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3105, d6125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25679 p hg
    simpa only [d3105, d6125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25681 (p : Pattern) (guard : d5540 p = 1) : d3106 p ≤ (2 : Int) + d6235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3106, d6235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25660 p hg
    simpa only [d3106, d6235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3106, d6235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25398 p hg
    simpa only [d3106, d6235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25682 (p : Pattern) (guard : d5540 p = 1) : d3107 p ≤ (2 : Int) + d6236 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3107, d6236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25663 p hg
    simpa only [d3107, d6236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3107, d6236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25446 p hg
    simpa only [d3107, d6236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25683 (p : Pattern) (guard : d5540 p = 1) : d3108 p ≤ (2 : Int) + d6237 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3108, d6237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25681 p hg
    simpa only [d3108, d6237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3108, d6237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25682 p hg
    simpa only [d3108, d6237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25684 (p : Pattern) (guard : d5540 p = 1) : d3109 p ≤ (2 : Int) + d6238 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3109, d6238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25663 p hg
    simpa only [d3109, d6238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3109, d6238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3109, d6238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25685 (p : Pattern) (guard : d5540 p = 1) : d3110 p ≤ (2 : Int) + d6239 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3110, d6239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25684 p hg
    simpa only [d3110, d6239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3110, d6239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3110, d6239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25686 (p : Pattern) (guard : d5540 p = 1) : d3111 p ≤ (2 : Int) + d6240 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3111, d6240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25683 p hg
    simpa only [d3111, d6240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3111, d6240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25685 p hg
    simpa only [d3111, d6240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25687 (p : Pattern) (guard : d5540 p = 1) : d3112 p ≤ (2 : Int) + d6241 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3112, d6241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25680 p hg
    simpa only [d3112, d6241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3112, d6241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25686 p hg
    simpa only [d3112, d6241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25688 (p : Pattern) (guard : d5540 p = 1) : d3113 p ≤ (2 : Int) + d6242 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3113, d6242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25669 p hg
    simpa only [d3113, d6242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3113, d6242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25687 p hg
    simpa only [d3113, d6242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25689 (p : Pattern) (guard : d5540 p = 1) : d3114 p ≤ (2 : Int) + d6044 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3114, d6044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25322 p hg
    simpa only [d3114, d6044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3114, d6044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d3114, d6044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25690 (p : Pattern) (guard : d5540 p = 1) : d2049 p ≤ (2 : Int) + d6102 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2049, d6102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25453 p hg
    simpa only [d2049, d6102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2049, d6102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2049, d6102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25691 (p : Pattern) (guard : d5540 p = 1) : d3115 p ≤ (2 : Int) + d6103 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3115, d6103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25689 p hg
    simpa only [d3115, d6103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3115, d6103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25690 p hg
    simpa only [d3115, d6103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25692 (p : Pattern) (guard : d5540 p = 1) : d2055 p ≤ (2 : Int) + d6102 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2055, d6102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d2055, d6102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2055, d6102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2055, d6102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25693 (p : Pattern) (guard : d5540 p = 1) : d3116 p ≤ (2 : Int) + d6103 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3116, d6103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25371 p hg
    simpa only [d3116, d6103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3116, d6103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25692 p hg
    simpa only [d3116, d6103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25694 (p : Pattern) (guard : d5540 p = 1) : d3117 p ≤ (2 : Int) + d6103 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25691 p hg
    simpa only [d3117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25693 p hg
    simpa only [d3117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25695 (p : Pattern) (guard : d5540 p = 1) : d3118 p ≤ (2 : Int) + d6243 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3118, d6243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25694 p hg
    simpa only [d3118, d6243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3118, d6243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d3118, d6243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25696 (p : Pattern) (guard : d5540 p = 1) : d3119 p ≤ (2 : Int) + d6244 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3119, d6244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25695 p hg
    simpa only [d3119, d6244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3119, d6244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25481 p hg
    simpa only [d3119, d6244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25697 (p : Pattern) (guard : d5540 p = 1) : d191 p ≤ (2 : Int) + d191 p := by
  omega
theorem compare25698 (p : Pattern) (guard : d0 p = 1) : d191 p ≤ (2 : Int) + d315 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25699 (p : Pattern) (guard : d1 p = 1) : d315 p ≤ (2 : Int) + d315 p := by
  omega
theorem compare25700 (p : Pattern) (guard : d5501 p = 1) : d2060 p ≤ (2 : Int) + d315 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25698 p hg
    simpa only [d5501, d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25699 p hg
    simpa only [d5501, d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25701 (p : Pattern) (guard : d0 p = 1) : d315 p ≤ (2 : Int) + d315 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25702 (p : Pattern) (guard : d5540 p = 1) : d2061 p ≤ (2 : Int) + d315 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25700 p hg
    simpa only [d5540, d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25701 p hg
    simpa only [d5540, d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25703 (p : Pattern) (guard : d5540 p = 1) : d3120 p ≤ (2 : Int) + d6245 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3120, d6245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25697 p hg
    simpa only [d3120, d6245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3120, d6245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25702 p hg
    simpa only [d3120, d6245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25704 (p : Pattern) (guard : d5540 p = 1) : d2062 p ≤ (2 : Int) + d6246 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2062, d6246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25702 p hg
    simpa only [d2062, d6246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2062, d6246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2062, d6246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25705 (p : Pattern) (guard : d5540 p = 1) : d3121 p ≤ (2 : Int) + d6247 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3121, d6247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25703 p hg
    simpa only [d3121, d6247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3121, d6247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25704 p hg
    simpa only [d3121, d6247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25706 (p : Pattern) (guard : d5540 p = 1) : d3122 p ≤ (2 : Int) + d6248 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3122, d6248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d3122, d6248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3122, d6248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25705 p hg
    simpa only [d3122, d6248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25707 (p : Pattern) (guard : d5540 p = 1) : d3123 p ≤ (2 : Int) + d6249 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3123, d6249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25706 p hg
    simpa only [d3123, d6249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3123, d6249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3123, d6249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25708 (p : Pattern) (guard : d5540 p = 1) : d3124 p ≤ (2 : Int) + d6250 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3124, d6250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25707 p hg
    simpa only [d3124, d6250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3124, d6250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3124, d6250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25709 (p : Pattern) (guard : d5540 p = 1) : d3125 p ≤ (2 : Int) + d6251 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3125, d6251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25696 p hg
    simpa only [d3125, d6251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3125, d6251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25708 p hg
    simpa only [d3125, d6251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25710 (p : Pattern) (guard : d0 p = 1) : d2070 p ≤ (2 : Int) + d1714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25711 (p : Pattern) (guard : d5540 p = 1) : d2071 p ≤ (2 : Int) + d1714 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25373 p hg
    simpa only [d5540, d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25710 p hg
    simpa only [d5540, d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25712 (p : Pattern) (guard : d5540 p = 1) : d2072 p ≤ (2 : Int) + d6058 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2072, d6058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25711 p hg
    simpa only [d2072, d6058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2072, d6058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2072, d6058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25713 (p : Pattern) (guard : d5540 p = 1) : d3126 p ≤ (2 : Int) + d6113 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3126, d6113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25439 p hg
    simpa only [d3126, d6113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3126, d6113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25712 p hg
    simpa only [d3126, d6113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25714 (p : Pattern) (guard : d5540 p = 1) : d3127 p ≤ (2 : Int) + d6113 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25713 p hg
    simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25715 (p : Pattern) (guard : d5540 p = 1) : d3128 p ≤ (2 : Int) + d6252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3128, d6252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d3128, d6252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3128, d6252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25435 p hg
    simpa only [d3128, d6252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25716 (p : Pattern) (guard : d5540 p = 1) : d3129 p ≤ (2 : Int) + d6253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3129, d6253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25714 p hg
    simpa only [d3129, d6253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3129, d6253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25715 p hg
    simpa only [d3129, d6253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25717 (p : Pattern) (guard : d5540 p = 1) : d3130 p ≤ (2 : Int) + d6254 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3130, d6254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25716 p hg
    simpa only [d3130, d6254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3130, d6254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25491 p hg
    simpa only [d3130, d6254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25718 (p : Pattern) (guard : d5540 p = 1) : d3131 p ≤ (2 : Int) + d6255 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3131, d6255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25705 p hg
    simpa only [d3131, d6255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3131, d6255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3131, d6255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25719 (p : Pattern) (guard : d5540 p = 1) : d3132 p ≤ (2 : Int) + d6256 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3132, d6256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25718 p hg
    simpa only [d3132, d6256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3132, d6256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3132, d6256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25720 (p : Pattern) (guard : d5540 p = 1) : d3133 p ≤ (2 : Int) + d6257 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3133, d6257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25719 p hg
    simpa only [d3133, d6257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3133, d6257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3133, d6257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25721 (p : Pattern) (guard : d5540 p = 1) : d3134 p ≤ (2 : Int) + d6258 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3134, d6258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25717 p hg
    simpa only [d3134, d6258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3134, d6258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25720 p hg
    simpa only [d3134, d6258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25722 (p : Pattern) (guard : d5540 p = 1) : d3135 p ≤ (2 : Int) + d6259 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3135, d6259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25709 p hg
    simpa only [d3135, d6259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3135, d6259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25721 p hg
    simpa only [d3135, d6259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25723 (p : Pattern) (guard : d5540 p = 1) : d3136 p ≤ (2 : Int) + d6260 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3136, d6260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25688 p hg
    simpa only [d3136, d6260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3136, d6260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25722 p hg
    simpa only [d3136, d6260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25724 (p : Pattern) (guard : d5540 p = 1) : d3137 p ≤ (2 : Int) + d6261 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3137, d6261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25722 p hg
    simpa only [d3137, d6261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3137, d6261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3137, d6261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25725 (p : Pattern) (guard : d5540 p = 1) : d3138 p ≤ (2 : Int) + d6262 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3138, d6262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25723 p hg
    simpa only [d3138, d6262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3138, d6262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25724 p hg
    simpa only [d3138, d6262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25726 (p : Pattern) (guard : d5540 p = 1) : d3139 p ≤ (2 : Int) + d6263 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3139, d6263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25505 p hg
    simpa only [d3139, d6263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3139, d6263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25725 p hg
    simpa only [d3139, d6263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25727 (p : Pattern) (guard : d5540 p = 1) : d3140 p ≤ (2 : Int) + d6264 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3140, d6264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d3140, d6264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3140, d6264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25726 p hg
    simpa only [d3140, d6264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25728 (p : Pattern) (guard : d5540 p = 1) : d3141 p ≤ (2 : Int) + d6265 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3141, d6265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25534 p hg
    simpa only [d3141, d6265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3141, d6265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3141, d6265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25729 (p : Pattern) (guard : d5540 p = 1) : d3142 p ≤ (2 : Int) + d6266 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3142, d6266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25583 p hg
    simpa only [d3142, d6266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3142, d6266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25728 p hg
    simpa only [d3142, d6266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25730 (p : Pattern) (guard : d5540 p = 1) : d3143 p ≤ (2 : Int) + d6267 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3143, d6267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25728 p hg
    simpa only [d3143, d6267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3143, d6267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3143, d6267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25731 (p : Pattern) (guard : d5540 p = 1) : d3144 p ≤ (2 : Int) + d6268 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3144, d6268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25729 p hg
    simpa only [d3144, d6268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3144, d6268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25730 p hg
    simpa only [d3144, d6268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25732 (p : Pattern) (guard : d5540 p = 1) : d3145 p ≤ (2 : Int) + d6269 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3145, d6269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25564 p hg
    simpa only [d3145, d6269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3145, d6269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3145, d6269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25733 (p : Pattern) (guard : d5540 p = 1) : d3146 p ≤ (2 : Int) + d6270 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3146, d6270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25591 p hg
    simpa only [d3146, d6270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3146, d6270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25732 p hg
    simpa only [d3146, d6270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25734 (p : Pattern) (guard : d5540 p = 1) : d3147 p ≤ (2 : Int) + d6271 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3147, d6271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25732 p hg
    simpa only [d3147, d6271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3147, d6271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3147, d6271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25735 (p : Pattern) (guard : d5540 p = 1) : d3148 p ≤ (2 : Int) + d6272 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3148, d6272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25733 p hg
    simpa only [d3148, d6272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3148, d6272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25734 p hg
    simpa only [d3148, d6272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25736 (p : Pattern) (guard : d5540 p = 1) : d3149 p ≤ (2 : Int) + d6273 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3149, d6273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25731 p hg
    simpa only [d3149, d6273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3149, d6273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25735 p hg
    simpa only [d3149, d6273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25737 (p : Pattern) (guard : d5540 p = 1) : d3150 p ≤ (2 : Int) + d6274 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3150, d6274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25570 p hg
    simpa only [d3150, d6274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3150, d6274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25736 p hg
    simpa only [d3150, d6274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25738 (p : Pattern) (guard : d5540 p = 1) : d3151 p ≤ (2 : Int) + d6275 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3151, d6275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25615 p hg
    simpa only [d3151, d6275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3151, d6275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3151, d6275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25739 (p : Pattern) (guard : d5540 p = 1) : d3152 p ≤ (2 : Int) + d6276 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3152, d6276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25628 p hg
    simpa only [d3152, d6276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3152, d6276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25738 p hg
    simpa only [d3152, d6276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25740 (p : Pattern) (guard : d5540 p = 1) : d3153 p ≤ (2 : Int) + d6277 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3153, d6277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25738 p hg
    simpa only [d3153, d6277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3153, d6277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3153, d6277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25741 (p : Pattern) (guard : d5540 p = 1) : d3154 p ≤ (2 : Int) + d6278 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3154, d6278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25739 p hg
    simpa only [d3154, d6278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3154, d6278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25740 p hg
    simpa only [d3154, d6278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25742 (p : Pattern) (guard : d5540 p = 1) : d3155 p ≤ (2 : Int) + d6279 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3155, d6279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25741 p hg
    simpa only [d3155, d6279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3155, d6279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25636 p hg
    simpa only [d3155, d6279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25743 (p : Pattern) (guard : d5540 p = 1) : d3156 p ≤ (2 : Int) + d6280 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3156, d6280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25627 p hg
    simpa only [d3156, d6280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3156, d6280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25742 p hg
    simpa only [d3156, d6280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25744 (p : Pattern) (guard : d5540 p = 1) : d3157 p ≤ (2 : Int) + d6281 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3157, d6281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25737 p hg
    simpa only [d3157, d6281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3157, d6281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25743 p hg
    simpa only [d3157, d6281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25745 (p : Pattern) (guard : d5540 p = 1) : d3158 p ≤ (2 : Int) + d6282 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3158, d6282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25743 p hg
    simpa only [d3158, d6282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3158, d6282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25643 p hg
    simpa only [d3158, d6282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25746 (p : Pattern) (guard : d5540 p = 1) : d3159 p ≤ (2 : Int) + d6283 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3159, d6283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25744 p hg
    simpa only [d3159, d6283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3159, d6283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25745 p hg
    simpa only [d3159, d6283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25747 (p : Pattern) (guard : d5540 p = 1) : d3160 p ≤ (2 : Int) + d6145 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3160, d6145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25509 p hg
    simpa only [d3160, d6145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3160, d6145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25608 p hg
    simpa only [d3160, d6145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25748 (p : Pattern) (guard : d5540 p = 1) : d2109 p ≤ (2 : Int) + d6187 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2109, d6187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25600 p hg
    simpa only [d2109, d6187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2109, d6187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2109, d6187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25749 (p : Pattern) (guard : d5540 p = 1) : d3161 p ≤ (2 : Int) + d6188 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3161, d6188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25747 p hg
    simpa only [d3161, d6188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3161, d6188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25748 p hg
    simpa only [d3161, d6188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25750 (p : Pattern) (guard : d5540 p = 1) : d3162 p ≤ (2 : Int) + d6191 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3162, d6191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25749 p hg
    simpa only [d3162, d6191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3162, d6191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25615 p hg
    simpa only [d3162, d6191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25751 (p : Pattern) (guard : d5540 p = 1) : d3163 p ≤ (2 : Int) + d6192 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3163, d6192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25603 p hg
    simpa only [d3163, d6192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3163, d6192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25750 p hg
    simpa only [d3163, d6192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25752 (p : Pattern) (guard : d5540 p = 1) : d3164 p ≤ (2 : Int) + d6191 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3164, d6191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25610 p hg
    simpa only [d3164, d6191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3164, d6191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25615 p hg
    simpa only [d3164, d6191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25753 (p : Pattern) (guard : d5540 p = 1) : d3165 p ≤ (2 : Int) + d6193 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3165, d6193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25752 p hg
    simpa only [d3165, d6193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3165, d6193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25537 p hg
    simpa only [d3165, d6193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25754 (p : Pattern) (guard : d5540 p = 1) : d3166 p ≤ (2 : Int) + d6194 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3166, d6194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25751 p hg
    simpa only [d3166, d6194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3166, d6194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25753 p hg
    simpa only [d3166, d6194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25755 (p : Pattern) (guard : d5540 p = 1) : d3167 p ≤ (2 : Int) + d6284 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3167, d6284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25589 p hg
    simpa only [d3167, d6284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3167, d6284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25556 p hg
    simpa only [d3167, d6284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25756 (p : Pattern) (guard : d5540 p = 1) : d3168 p ≤ (2 : Int) + d6285 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3168, d6285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25620 p hg
    simpa only [d3168, d6285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3168, d6285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25755 p hg
    simpa only [d3168, d6285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25757 (p : Pattern) (guard : d5540 p = 1) : d3169 p ≤ (2 : Int) + d6286 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3169, d6286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25756 p hg
    simpa only [d3169, d6286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3169, d6286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25732 p hg
    simpa only [d3169, d6286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25758 (p : Pattern) (guard : d5540 p = 1) : d3170 p ≤ (2 : Int) + d6287 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3170, d6287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25622 p hg
    simpa only [d3170, d6287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3170, d6287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3170, d6287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25759 (p : Pattern) (guard : d5540 p = 1) : d3171 p ≤ (2 : Int) + d6288 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3171, d6288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25758 p hg
    simpa only [d3171, d6288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3171, d6288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3171, d6288, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
