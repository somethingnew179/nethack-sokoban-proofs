/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons235
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare33040 (p : Pattern) (guard : d6558 p = 1) : d3052 p ≤ (2 : Int) + d7474 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3052, d7474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33039 p hg
    simpa only [d3052, d7474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3052, d7474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3052, d7474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33041 (p : Pattern) (guard : d6558 p = 1) : d3053 p ≤ (2 : Int) + d7475 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3053, d7475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33040 p hg
    simpa only [d3053, d7475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3053, d7475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3053, d7475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33042 (p : Pattern) (guard : d6558 p = 1) : d3054 p ≤ (2 : Int) + d7476 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3054, d7476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33035 p hg
    simpa only [d3054, d7476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3054, d7476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33041 p hg
    simpa only [d3054, d7476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33043 (p : Pattern) (guard : d6558 p = 1) : d3055 p ≤ (2 : Int) + d7477 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3055, d7477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33026 p hg
    simpa only [d3055, d7477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3055, d7477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33036 p hg
    simpa only [d3055, d7477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33044 (p : Pattern) (guard : d6558 p = 1) : d3056 p ≤ (2 : Int) + d7478 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3056, d7478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33031 p hg
    simpa only [d3056, d7478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3056, d7478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32806 p hg
    simpa only [d3056, d7478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33045 (p : Pattern) (guard : d6558 p = 1) : d3057 p ≤ (2 : Int) + d7479 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3057, d7479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33043 p hg
    simpa only [d3057, d7479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3057, d7479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33044 p hg
    simpa only [d3057, d7479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33046 (p : Pattern) (guard : d6558 p = 1) : d3058 p ≤ (2 : Int) + d7480 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3058, d7480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33031 p hg
    simpa only [d3058, d7480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3058, d7480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32809 p hg
    simpa only [d3058, d7480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33047 (p : Pattern) (guard : d6558 p = 1) : d3059 p ≤ (2 : Int) + d7481 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3059, d7481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33046 p hg
    simpa only [d3059, d7481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3059, d7481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3059, d7481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33048 (p : Pattern) (guard : d6558 p = 1) : d3060 p ≤ (2 : Int) + d7482 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3060, d7482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33045 p hg
    simpa only [d3060, d7482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3060, d7482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33047 p hg
    simpa only [d3060, d7482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33049 (p : Pattern) (guard : d6558 p = 1) : d3061 p ≤ (2 : Int) + d7483 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3061, d7483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33038 p hg
    simpa only [d3061, d7483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3061, d7483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3061, d7483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33050 (p : Pattern) (guard : d6558 p = 1) : d3062 p ≤ (2 : Int) + d7484 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3062, d7484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33049 p hg
    simpa only [d3062, d7484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3062, d7484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3062, d7484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33051 (p : Pattern) (guard : d6558 p = 1) : d3063 p ≤ (2 : Int) + d7485 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3063, d7485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33050 p hg
    simpa only [d3063, d7485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3063, d7485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3063, d7485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33052 (p : Pattern) (guard : d6558 p = 1) : d3064 p ≤ (2 : Int) + d7486 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3064, d7486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33048 p hg
    simpa only [d3064, d7486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3064, d7486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33051 p hg
    simpa only [d3064, d7486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33053 (p : Pattern) (guard : d6558 p = 1) : d3065 p ≤ (2 : Int) + d7487 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3065, d7487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33042 p hg
    simpa only [d3065, d7487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3065, d7487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33052 p hg
    simpa only [d3065, d7487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33054 (p : Pattern) (guard : d6558 p = 1) : d3066 p ≤ (2 : Int) + d7488 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3066, d7488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33009 p hg
    simpa only [d3066, d7488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3066, d7488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33053 p hg
    simpa only [d3066, d7488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33055 (p : Pattern) (guard : d6558 p = 1) : d3067 p ≤ (2 : Int) + d7489 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3067, d7489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32923 p hg
    simpa only [d3067, d7489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3067, d7489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3067, d7489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33056 (p : Pattern) (guard : d6558 p = 1) : d3068 p ≤ (2 : Int) + d7490 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3068, d7490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33055 p hg
    simpa only [d3068, d7490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3068, d7490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3068, d7490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33057 (p : Pattern) (guard : d6558 p = 1) : d3069 p ≤ (2 : Int) + d7491 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3069, d7491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33056 p hg
    simpa only [d3069, d7491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3069, d7491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3069, d7491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33058 (p : Pattern) (guard : d6558 p = 1) : d3070 p ≤ (2 : Int) + d7492 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3070, d7492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33057 p hg
    simpa only [d3070, d7492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3070, d7492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3070, d7492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33059 (p : Pattern) (guard : d6558 p = 1) : d3071 p ≤ (2 : Int) + d7493 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3071, d7493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33053 p hg
    simpa only [d3071, d7493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3071, d7493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33058 p hg
    simpa only [d3071, d7493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33060 (p : Pattern) (guard : d6558 p = 1) : d3072 p ≤ (2 : Int) + d7494 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3072, d7494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33054 p hg
    simpa only [d3072, d7494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3072, d7494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33059 p hg
    simpa only [d3072, d7494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33061 (p : Pattern) (guard : d6558 p = 1) : d3073 p ≤ (2 : Int) + d7495 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3073, d7495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33053 p hg
    simpa only [d3073, d7495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3073, d7495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3073, d7495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33062 (p : Pattern) (guard : d6558 p = 1) : d3074 p ≤ (2 : Int) + d7496 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3074, d7496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33054 p hg
    simpa only [d3074, d7496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3074, d7496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33061 p hg
    simpa only [d3074, d7496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33063 (p : Pattern) (guard : d6558 p = 1) : d3075 p ≤ (2 : Int) + d7497 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3075, d7497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33060 p hg
    simpa only [d3075, d7497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3075, d7497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33062 p hg
    simpa only [d3075, d7497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33064 (p : Pattern) (guard : d6558 p = 1) : d3076 p ≤ (2 : Int) + d7498 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3076, d7498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32886 p hg
    simpa only [d3076, d7498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3076, d7498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33063 p hg
    simpa only [d3076, d7498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33065 (p : Pattern) (guard : d6558 p = 1) : d3077 p ≤ (2 : Int) + d7499 p := by
  cases selected : p 49 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3077, d7499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32886 p hg
    simpa only [d3077, d7499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3077, d7499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33064 p hg
    simpa only [d3077, d7499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33066 (p : Pattern) (guard : d6558 p = 1) : d3078 p ≤ (2 : Int) + d7500 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3078, d7500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32680 p hg
    simpa only [d3078, d7500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3078, d7500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32766 p hg
    simpa only [d3078, d7500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33067 (p : Pattern) (guard : d6558 p = 1) : d3079 p ≤ (2 : Int) + d7501 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3079, d7501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32767 p hg
    simpa only [d3079, d7501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3079, d7501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33066 p hg
    simpa only [d3079, d7501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33068 (p : Pattern) (guard : d6558 p = 1) : d3080 p ≤ (2 : Int) + d7502 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3080, d7502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32676 p hg
    simpa only [d3080, d7502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3080, d7502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33067 p hg
    simpa only [d3080, d7502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33069 (p : Pattern) (guard : d6558 p = 1) : d2013 p ≤ (2 : Int) + d7503 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2013, d7503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32682 p hg
    simpa only [d2013, d7503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2013, d7503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2013, d7503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33070 (p : Pattern) (guard : d6558 p = 1) : d3081 p ≤ (2 : Int) + d7504 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3081, d7504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33068 p hg
    simpa only [d3081, d7504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3081, d7504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33069 p hg
    simpa only [d3081, d7504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33071 (p : Pattern) (guard : d6558 p = 1) : d3082 p ≤ (2 : Int) + d7505 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3082, d7505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32830 p hg
    simpa only [d3082, d7505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3082, d7505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33070 p hg
    simpa only [d3082, d7505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33072 (p : Pattern) (guard : d6558 p = 1) : d3083 p ≤ (2 : Int) + d7506 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3083, d7506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32830 p hg
    simpa only [d3083, d7506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3083, d7506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33071 p hg
    simpa only [d3083, d7506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33073 (p : Pattern) (guard : d6558 p = 1) : d3084 p ≤ (2 : Int) + d7507 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3084, d7507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33071 p hg
    simpa only [d3084, d7507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3084, d7507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32852 p hg
    simpa only [d3084, d7507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33074 (p : Pattern) (guard : d6558 p = 1) : d3085 p ≤ (2 : Int) + d7508 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3085, d7508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33072 p hg
    simpa only [d3085, d7508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3085, d7508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33073 p hg
    simpa only [d3085, d7508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33075 (p : Pattern) (guard : d6558 p = 1) : d3086 p ≤ (2 : Int) + d7509 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3086, d7509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32813 p hg
    simpa only [d3086, d7509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3086, d7509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32752 p hg
    simpa only [d3086, d7509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33076 (p : Pattern) (guard : d6558 p = 1) : d3087 p ≤ (2 : Int) + d7510 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3087, d7510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32855 p hg
    simpa only [d3087, d7510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3087, d7510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33075 p hg
    simpa only [d3087, d7510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33077 (p : Pattern) (guard : d6558 p = 1) : d3088 p ≤ (2 : Int) + d7511 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3088, d7511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32813 p hg
    simpa only [d3088, d7511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3088, d7511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32762 p hg
    simpa only [d3088, d7511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33078 (p : Pattern) (guard : d6558 p = 1) : d3089 p ≤ (2 : Int) + d7512 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3089, d7512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32856 p hg
    simpa only [d3089, d7512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3089, d7512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3089, d7512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33079 (p : Pattern) (guard : d6558 p = 1) : d3090 p ≤ (2 : Int) + d7513 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3090, d7513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33077 p hg
    simpa only [d3090, d7513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3090, d7513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33078 p hg
    simpa only [d3090, d7513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33080 (p : Pattern) (guard : d6558 p = 1) : d3091 p ≤ (2 : Int) + d7514 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3091, d7514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33076 p hg
    simpa only [d3091, d7514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3091, d7514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33079 p hg
    simpa only [d3091, d7514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33081 (p : Pattern) (guard : d6558 p = 1) : d3092 p ≤ (2 : Int) + d7515 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3092, d7515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32814 p hg
    simpa only [d3092, d7515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3092, d7515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33078 p hg
    simpa only [d3092, d7515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33082 (p : Pattern) (guard : d6558 p = 1) : d3093 p ≤ (2 : Int) + d7516 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3093, d7516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33081 p hg
    simpa only [d3093, d7516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3093, d7516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32821 p hg
    simpa only [d3093, d7516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33083 (p : Pattern) (guard : d6558 p = 1) : d3094 p ≤ (2 : Int) + d7517 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3094, d7517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33080 p hg
    simpa only [d3094, d7517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3094, d7517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33082 p hg
    simpa only [d3094, d7517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33084 (p : Pattern) (guard : d6558 p = 1) : d3095 p ≤ (2 : Int) + d7518 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3095, d7518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33074 p hg
    simpa only [d3095, d7518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3095, d7518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33083 p hg
    simpa only [d3095, d7518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33085 (p : Pattern) (guard : d6558 p = 1) : d3096 p ≤ (2 : Int) + d7519 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3096, d7519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32732 p hg
    simpa only [d3096, d7519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3096, d7519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32728 p hg
    simpa only [d3096, d7519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33086 (p : Pattern) (guard : d6558 p = 1) : d3097 p ≤ (2 : Int) + d7520 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3097, d7520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32729 p hg
    simpa only [d3097, d7520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3097, d7520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33085 p hg
    simpa only [d3097, d7520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33087 (p : Pattern) (guard : d6558 p = 1) : d3098 p ≤ (2 : Int) + d7521 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3098, d7521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32725 p hg
    simpa only [d3098, d7521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3098, d7521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33086 p hg
    simpa only [d3098, d7521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33088 (p : Pattern) (guard : d6558 p = 1) : d2031 p ≤ (2 : Int) + d7522 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2031, d7522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32785 p hg
    simpa only [d2031, d7522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2031, d7522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2031, d7522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33089 (p : Pattern) (guard : d6558 p = 1) : d3099 p ≤ (2 : Int) + d7523 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3099, d7523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33087 p hg
    simpa only [d3099, d7523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3099, d7523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33088 p hg
    simpa only [d3099, d7523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33090 (p : Pattern) (guard : d6558 p = 1) : d3100 p ≤ (2 : Int) + d7524 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3100, d7524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32830 p hg
    simpa only [d3100, d7524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3100, d7524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33089 p hg
    simpa only [d3100, d7524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33091 (p : Pattern) (guard : d6558 p = 1) : d3101 p ≤ (2 : Int) + d7525 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3101, d7525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33070 p hg
    simpa only [d3101, d7525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3101, d7525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32851 p hg
    simpa only [d3101, d7525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33092 (p : Pattern) (guard : d6558 p = 1) : d3102 p ≤ (2 : Int) + d7526 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3102, d7526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33090 p hg
    simpa only [d3102, d7526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3102, d7526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33091 p hg
    simpa only [d3102, d7526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33093 (p : Pattern) (guard : d6558 p = 1) : d3103 p ≤ (2 : Int) + d7527 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3103, d7527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33070 p hg
    simpa only [d3103, d7527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3103, d7527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32806 p hg
    simpa only [d3103, d7527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33094 (p : Pattern) (guard : d6558 p = 1) : d3104 p ≤ (2 : Int) + d7528 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3104, d7528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33093 p hg
    simpa only [d3104, d7528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3104, d7528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32810 p hg
    simpa only [d3104, d7528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33095 (p : Pattern) (guard : d6558 p = 1) : d3105 p ≤ (2 : Int) + d7529 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3105, d7529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33092 p hg
    simpa only [d3105, d7529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3105, d7529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33094 p hg
    simpa only [d3105, d7529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33096 (p : Pattern) (guard : d6558 p = 1) : d3106 p ≤ (2 : Int) + d7530 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3106, d7530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33075 p hg
    simpa only [d3106, d7530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3106, d7530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32774 p hg
    simpa only [d3106, d7530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33097 (p : Pattern) (guard : d6558 p = 1) : d3107 p ≤ (2 : Int) + d7531 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3107, d7531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33078 p hg
    simpa only [d3107, d7531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3107, d7531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32820 p hg
    simpa only [d3107, d7531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33098 (p : Pattern) (guard : d6558 p = 1) : d3108 p ≤ (2 : Int) + d7532 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3108, d7532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33096 p hg
    simpa only [d3108, d7532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3108, d7532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33097 p hg
    simpa only [d3108, d7532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33099 (p : Pattern) (guard : d6558 p = 1) : d3109 p ≤ (2 : Int) + d7533 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3109, d7533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33078 p hg
    simpa only [d3109, d7533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3109, d7533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3109, d7533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33100 (p : Pattern) (guard : d6558 p = 1) : d3110 p ≤ (2 : Int) + d7534 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3110, d7534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33099 p hg
    simpa only [d3110, d7534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3110, d7534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3110, d7534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33101 (p : Pattern) (guard : d6558 p = 1) : d3111 p ≤ (2 : Int) + d7535 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3111, d7535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33098 p hg
    simpa only [d3111, d7535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3111, d7535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33100 p hg
    simpa only [d3111, d7535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33102 (p : Pattern) (guard : d6558 p = 1) : d3112 p ≤ (2 : Int) + d7536 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3112, d7536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33095 p hg
    simpa only [d3112, d7536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3112, d7536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33101 p hg
    simpa only [d3112, d7536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33103 (p : Pattern) (guard : d6558 p = 1) : d3113 p ≤ (2 : Int) + d7537 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3113, d7537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33084 p hg
    simpa only [d3113, d7537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3113, d7537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33102 p hg
    simpa only [d3113, d7537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33104 (p : Pattern) (guard : d6558 p = 1) : d3114 p ≤ (2 : Int) + d7538 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3114, d7538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32658 p hg
    simpa only [d3114, d7538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3114, d7538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32840 p hg
    simpa only [d3114, d7538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33105 (p : Pattern) (guard : d6558 p = 1) : d2049 p ≤ (2 : Int) + d7539 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2049, d7539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32827 p hg
    simpa only [d2049, d7539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2049, d7539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2049, d7539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33106 (p : Pattern) (guard : d6558 p = 1) : d3115 p ≤ (2 : Int) + d7540 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3115, d7540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33104 p hg
    simpa only [d3115, d7540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3115, d7540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33105 p hg
    simpa only [d3115, d7540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33107 (p : Pattern) (guard : d6558 p = 1) : d2055 p ≤ (2 : Int) + d7345 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2055, d7345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32834 p hg
    simpa only [d2055, d7345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2055, d7345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2055, d7345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33108 (p : Pattern) (guard : d6558 p = 1) : d3116 p ≤ (2 : Int) + d7346 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3116, d7346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32723 p hg
    simpa only [d3116, d7346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3116, d7346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33107 p hg
    simpa only [d3116, d7346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33109 (p : Pattern) (guard : d6558 p = 1) : d3117 p ≤ (2 : Int) + d7541 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3117, d7541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33106 p hg
    simpa only [d3117, d7541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3117, d7541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33108 p hg
    simpa only [d3117, d7541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33110 (p : Pattern) (guard : d6558 p = 1) : d3118 p ≤ (2 : Int) + d7542 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3118, d7542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33109 p hg
    simpa only [d3118, d7542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3118, d7542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32858 p hg
    simpa only [d3118, d7542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33111 (p : Pattern) (guard : d6558 p = 1) : d3119 p ≤ (2 : Int) + d7543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3119, d7543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33110 p hg
    simpa only [d3119, d7543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3119, d7543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32859 p hg
    simpa only [d3119, d7543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33112 (p : Pattern) (guard : d5842 p = 1) : d8 p ≤ (2 : Int) + d8 p := by
  omega
theorem compare33113 (p : Pattern) (guard : d6558 p = 1) : d191 p ≤ (2 : Int) + d8 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33112 p hg
    simpa only [d6558, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32679 p hg
    simpa only [d6558, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33114 (p : Pattern) (guard : d0 p = 1) : d8 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33115 (p : Pattern) (guard : d5842 p = 1) : d190 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33114 p hg
    simpa only [d5842, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d5842, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33116 (p : Pattern) (guard : d6558 p = 1) : d315 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33115 p hg
    simpa only [d6558, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d6558, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33117 (p : Pattern) (guard : d6558 p = 1) : d2060 p ≤ (2 : Int) + d7291 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2060, d7291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33113 p hg
    simpa only [d2060, d7291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2060, d7291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33116 p hg
    simpa only [d2060, d7291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33118 (p : Pattern) (guard : d6558 p = 1) : d2061 p ≤ (2 : Int) + d7544 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2061, d7544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33117 p hg
    simpa only [d2061, d7544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2061, d7544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33116 p hg
    simpa only [d2061, d7544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33119 (p : Pattern) (guard : d6558 p = 1) : d3120 p ≤ (2 : Int) + d7545 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3120, d7545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33113 p hg
    simpa only [d3120, d7545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3120, d7545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33118 p hg
    simpa only [d3120, d7545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33120 (p : Pattern) (guard : d6558 p = 1) : d2062 p ≤ (2 : Int) + d7546 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2062, d7546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33118 p hg
    simpa only [d2062, d7546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2062, d7546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2062, d7546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33121 (p : Pattern) (guard : d6558 p = 1) : d3121 p ≤ (2 : Int) + d7547 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3121, d7547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33119 p hg
    simpa only [d3121, d7547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3121, d7547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33120 p hg
    simpa only [d3121, d7547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33122 (p : Pattern) (guard : d6558 p = 1) : d3122 p ≤ (2 : Int) + d7548 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3122, d7548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32847 p hg
    simpa only [d3122, d7548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3122, d7548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33121 p hg
    simpa only [d3122, d7548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33123 (p : Pattern) (guard : d6558 p = 1) : d3123 p ≤ (2 : Int) + d7549 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3123, d7549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33122 p hg
    simpa only [d3123, d7549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3123, d7549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3123, d7549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33124 (p : Pattern) (guard : d6558 p = 1) : d3124 p ≤ (2 : Int) + d7550 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3124, d7550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33123 p hg
    simpa only [d3124, d7550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3124, d7550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3124, d7550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33125 (p : Pattern) (guard : d6558 p = 1) : d3125 p ≤ (2 : Int) + d7551 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3125, d7551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33111 p hg
    simpa only [d3125, d7551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3125, d7551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33124 p hg
    simpa only [d3125, d7551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33126 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33127 (p : Pattern) (guard : d5842 p = 1) : d2068 p ≤ (2 : Int) + d10 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d2068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33126 p hg
    simpa only [d5842, d2068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d2068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15723 p hg
    simpa only [d5842, d2068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33128 (p : Pattern) (guard : d6558 p = 1) : d2069 p ≤ (2 : Int) + d10 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33127 p hg
    simpa only [d6558, d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32748 p hg
    simpa only [d6558, d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33129 (p : Pattern) (guard : d6558 p = 1) : d2070 p ≤ (2 : Int) + d7552 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2070, d7552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32732 p hg
    simpa only [d2070, d7552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2070, d7552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33128 p hg
    simpa only [d2070, d7552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33130 (p : Pattern) (guard : d6558 p = 1) : d2071 p ≤ (2 : Int) + d7553 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2071, d7553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32729 p hg
    simpa only [d2071, d7553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2071, d7553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33129 p hg
    simpa only [d2071, d7553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33131 (p : Pattern) (guard : d6558 p = 1) : d2072 p ≤ (2 : Int) + d7554 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2072, d7554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33130 p hg
    simpa only [d2072, d7554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2072, d7554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2072, d7554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33132 (p : Pattern) (guard : d6558 p = 1) : d3126 p ≤ (2 : Int) + d7555 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3126, d7555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32813 p hg
    simpa only [d3126, d7555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3126, d7555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33131 p hg
    simpa only [d3126, d7555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33133 (p : Pattern) (guard : d6558 p = 1) : d3127 p ≤ (2 : Int) + d7556 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3127, d7556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33132 p hg
    simpa only [d3127, d7556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3127, d7556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32855 p hg
    simpa only [d3127, d7556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33134 (p : Pattern) (guard : d6558 p = 1) : d3128 p ≤ (2 : Int) + d7557 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3128, d7557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32847 p hg
    simpa only [d3128, d7557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3128, d7557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32809 p hg
    simpa only [d3128, d7557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33135 (p : Pattern) (guard : d6558 p = 1) : d3129 p ≤ (2 : Int) + d7558 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3129, d7558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33133 p hg
    simpa only [d3129, d7558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3129, d7558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33134 p hg
    simpa only [d3129, d7558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33136 (p : Pattern) (guard : d6558 p = 1) : d3130 p ≤ (2 : Int) + d7559 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3130, d7559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33135 p hg
    simpa only [d3130, d7559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3130, d7559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32869 p hg
    simpa only [d3130, d7559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33137 (p : Pattern) (guard : d6558 p = 1) : d3131 p ≤ (2 : Int) + d7560 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3131, d7560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33121 p hg
    simpa only [d3131, d7560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3131, d7560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3131, d7560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33138 (p : Pattern) (guard : d6558 p = 1) : d3132 p ≤ (2 : Int) + d7561 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3132, d7561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33137 p hg
    simpa only [d3132, d7561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3132, d7561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3132, d7561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33139 (p : Pattern) (guard : d6558 p = 1) : d3133 p ≤ (2 : Int) + d7562 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3133, d7562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33138 p hg
    simpa only [d3133, d7562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3133, d7562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3133, d7562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33140 (p : Pattern) (guard : d6558 p = 1) : d3134 p ≤ (2 : Int) + d7563 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3134, d7563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33136 p hg
    simpa only [d3134, d7563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3134, d7563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33139 p hg
    simpa only [d3134, d7563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33141 (p : Pattern) (guard : d6558 p = 1) : d3135 p ≤ (2 : Int) + d7564 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3135, d7564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33125 p hg
    simpa only [d3135, d7564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3135, d7564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33140 p hg
    simpa only [d3135, d7564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33142 (p : Pattern) (guard : d6558 p = 1) : d3136 p ≤ (2 : Int) + d7565 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3136, d7565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33103 p hg
    simpa only [d3136, d7565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3136, d7565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33141 p hg
    simpa only [d3136, d7565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33143 (p : Pattern) (guard : d6558 p = 1) : d3137 p ≤ (2 : Int) + d7566 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3137, d7566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33141 p hg
    simpa only [d3137, d7566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3137, d7566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3137, d7566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33144 (p : Pattern) (guard : d6558 p = 1) : d3138 p ≤ (2 : Int) + d7567 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3138, d7567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33142 p hg
    simpa only [d3138, d7567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3138, d7567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33143 p hg
    simpa only [d3138, d7567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33145 (p : Pattern) (guard : d6558 p = 1) : d3139 p ≤ (2 : Int) + d7568 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3139, d7568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32883 p hg
    simpa only [d3139, d7568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3139, d7568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33144 p hg
    simpa only [d3139, d7568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33146 (p : Pattern) (guard : d6558 p = 1) : d3140 p ≤ (2 : Int) + d7569 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3140, d7569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32886 p hg
    simpa only [d3140, d7569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3140, d7569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33145 p hg
    simpa only [d3140, d7569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33147 (p : Pattern) (guard : d6558 p = 1) : d3141 p ≤ (2 : Int) + d7570 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3141, d7570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32920 p hg
    simpa only [d3141, d7570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3141, d7570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3141, d7570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33148 (p : Pattern) (guard : d6558 p = 1) : d3142 p ≤ (2 : Int) + d7571 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3142, d7571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32994 p hg
    simpa only [d3142, d7571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3142, d7571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33147 p hg
    simpa only [d3142, d7571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33149 (p : Pattern) (guard : d6558 p = 1) : d3143 p ≤ (2 : Int) + d7572 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3143, d7572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33147 p hg
    simpa only [d3143, d7572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3143, d7572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3143, d7572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33150 (p : Pattern) (guard : d6558 p = 1) : d3144 p ≤ (2 : Int) + d7573 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3144, d7573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33148 p hg
    simpa only [d3144, d7573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3144, d7573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33149 p hg
    simpa only [d3144, d7573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33151 (p : Pattern) (guard : d6558 p = 1) : d3145 p ≤ (2 : Int) + d7574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3145, d7574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32977 p hg
    simpa only [d3145, d7574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3145, d7574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3145, d7574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33152 (p : Pattern) (guard : d6558 p = 1) : d3146 p ≤ (2 : Int) + d7575 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3146, d7575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33002 p hg
    simpa only [d3146, d7575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3146, d7575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33151 p hg
    simpa only [d3146, d7575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33153 (p : Pattern) (guard : d6558 p = 1) : d3147 p ≤ (2 : Int) + d7576 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3147, d7576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33151 p hg
    simpa only [d3147, d7576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3147, d7576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3147, d7576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33154 (p : Pattern) (guard : d6558 p = 1) : d3148 p ≤ (2 : Int) + d7577 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3148, d7577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33152 p hg
    simpa only [d3148, d7577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3148, d7577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33153 p hg
    simpa only [d3148, d7577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33155 (p : Pattern) (guard : d6558 p = 1) : d3149 p ≤ (2 : Int) + d7578 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3149, d7578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33150 p hg
    simpa only [d3149, d7578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3149, d7578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33154 p hg
    simpa only [d3149, d7578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33156 (p : Pattern) (guard : d6558 p = 1) : d3150 p ≤ (2 : Int) + d7579 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3150, d7579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32983 p hg
    simpa only [d3150, d7579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3150, d7579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33155 p hg
    simpa only [d3150, d7579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33157 (p : Pattern) (guard : d6558 p = 1) : d3151 p ≤ (2 : Int) + d7580 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3151, d7580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33031 p hg
    simpa only [d3151, d7580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3151, d7580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3151, d7580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33158 (p : Pattern) (guard : d6558 p = 1) : d3152 p ≤ (2 : Int) + d7581 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3152, d7581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33043 p hg
    simpa only [d3152, d7581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3152, d7581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33157 p hg
    simpa only [d3152, d7581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33159 (p : Pattern) (guard : d6558 p = 1) : d3153 p ≤ (2 : Int) + d7582 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3153, d7582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33157 p hg
    simpa only [d3153, d7582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3153, d7582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3153, d7582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33160 (p : Pattern) (guard : d6558 p = 1) : d3154 p ≤ (2 : Int) + d7583 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3154, d7583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33158 p hg
    simpa only [d3154, d7583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3154, d7583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33159 p hg
    simpa only [d3154, d7583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33161 (p : Pattern) (guard : d6558 p = 1) : d3155 p ≤ (2 : Int) + d7584 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3155, d7584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33160 p hg
    simpa only [d3155, d7584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3155, d7584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33051 p hg
    simpa only [d3155, d7584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33162 (p : Pattern) (guard : d6558 p = 1) : d3156 p ≤ (2 : Int) + d7585 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3156, d7585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33042 p hg
    simpa only [d3156, d7585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3156, d7585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33161 p hg
    simpa only [d3156, d7585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33163 (p : Pattern) (guard : d6558 p = 1) : d3157 p ≤ (2 : Int) + d7586 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3157, d7586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33156 p hg
    simpa only [d3157, d7586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3157, d7586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33162 p hg
    simpa only [d3157, d7586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33164 (p : Pattern) (guard : d6558 p = 1) : d3158 p ≤ (2 : Int) + d7587 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3158, d7587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33162 p hg
    simpa only [d3158, d7587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3158, d7587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33058 p hg
    simpa only [d3158, d7587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33165 (p : Pattern) (guard : d6558 p = 1) : d3159 p ≤ (2 : Int) + d7588 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3159, d7588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33163 p hg
    simpa only [d3159, d7588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3159, d7588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33164 p hg
    simpa only [d3159, d7588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33166 (p : Pattern) (guard : d6558 p = 1) : d3160 p ≤ (2 : Int) + d7589 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3160, d7589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32889 p hg
    simpa only [d3160, d7589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3160, d7589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33024 p hg
    simpa only [d3160, d7589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33167 (p : Pattern) (guard : d6558 p = 1) : d2109 p ≤ (2 : Int) + d7590 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2109, d7590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33011 p hg
    simpa only [d2109, d7590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2109, d7590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2109, d7590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33168 (p : Pattern) (guard : d6558 p = 1) : d3161 p ≤ (2 : Int) + d7591 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3161, d7591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33166 p hg
    simpa only [d3161, d7591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3161, d7591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33167 p hg
    simpa only [d3161, d7591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33169 (p : Pattern) (guard : d6558 p = 1) : d3162 p ≤ (2 : Int) + d7592 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3162, d7592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33168 p hg
    simpa only [d3162, d7592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3162, d7592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33031 p hg
    simpa only [d3162, d7592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33170 (p : Pattern) (guard : d6558 p = 1) : d3163 p ≤ (2 : Int) + d7593 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3163, d7593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33014 p hg
    simpa only [d3163, d7593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3163, d7593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33169 p hg
    simpa only [d3163, d7593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33171 (p : Pattern) (guard : d6558 p = 1) : d3164 p ≤ (2 : Int) + d7594 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3164, d7594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33026 p hg
    simpa only [d3164, d7594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3164, d7594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33031 p hg
    simpa only [d3164, d7594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33172 (p : Pattern) (guard : d6558 p = 1) : d3165 p ≤ (2 : Int) + d7595 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3165, d7595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33171 p hg
    simpa only [d3165, d7595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3165, d7595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32923 p hg
    simpa only [d3165, d7595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33173 (p : Pattern) (guard : d6558 p = 1) : d3166 p ≤ (2 : Int) + d7596 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3166, d7596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33170 p hg
    simpa only [d3166, d7596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3166, d7596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33172 p hg
    simpa only [d3166, d7596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33174 (p : Pattern) (guard : d6558 p = 1) : d3167 p ≤ (2 : Int) + d7597 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3167, d7597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33000 p hg
    simpa only [d3167, d7597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3167, d7597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32963 p hg
    simpa only [d3167, d7597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33175 (p : Pattern) (guard : d6558 p = 1) : d3168 p ≤ (2 : Int) + d7598 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3168, d7598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33036 p hg
    simpa only [d3168, d7598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3168, d7598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33174 p hg
    simpa only [d3168, d7598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33176 (p : Pattern) (guard : d6558 p = 1) : d3169 p ≤ (2 : Int) + d7599 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3169, d7599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33175 p hg
    simpa only [d3169, d7599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3169, d7599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33151 p hg
    simpa only [d3169, d7599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33177 (p : Pattern) (guard : d6558 p = 1) : d3170 p ≤ (2 : Int) + d7600 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3170, d7600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33037 p hg
    simpa only [d3170, d7600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3170, d7600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3170, d7600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33178 (p : Pattern) (guard : d6558 p = 1) : d3171 p ≤ (2 : Int) + d7601 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3171, d7601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33177 p hg
    simpa only [d3171, d7601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3171, d7601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3171, d7601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33179 (p : Pattern) (guard : d6558 p = 1) : d3172 p ≤ (2 : Int) + d7602 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3172, d7602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33178 p hg
    simpa only [d3172, d7602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3172, d7602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3172, d7602, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
