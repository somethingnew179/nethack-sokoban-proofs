/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2940 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d59 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2941 (p : Pattern) (guard : d4206 p = 1) : d70 p ≤ (0 : Int) + d59 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2939 p hg
    simpa only [d4206, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2940 p hg
    simpa only [d4206, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2942 (p : Pattern) (guard : d4206 p = 1) : d71 p ≤ (0 : Int) + d4217 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d71, d4217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2918 p hg
    simpa only [d71, d4217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d71, d4217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2941 p hg
    simpa only [d71, d4217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2943 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2944 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d41 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2945 (p : Pattern) (guard : d4206 p = 1) : d72 p ≤ (0 : Int) + d41 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2943 p hg
    simpa only [d4206, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2944 p hg
    simpa only [d4206, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2946 (p : Pattern) (guard : d4206 p = 1) : d73 p ≤ (0 : Int) + d4218 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d73, d4218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2945 p hg
    simpa only [d73, d4218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d73, d4218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d73, d4218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2947 (p : Pattern) (guard : d4206 p = 1) : d74 p ≤ (0 : Int) + d4219 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d74, d4219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2942 p hg
    simpa only [d74, d4219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d74, d4219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2946 p hg
    simpa only [d74, d4219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2948 (p : Pattern) (guard : d4206 p = 1) : d75 p ≤ (0 : Int) + d4220 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d75, d4220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2938 p hg
    simpa only [d75, d4220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d75, d4220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2947 p hg
    simpa only [d75, d4220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2949 (p : Pattern) (guard : d4207 p = 1) : d76 p ≤ (0 : Int) + d4220 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2932 p hg
    simpa only [d4207, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2948 p hg
    simpa only [d4207, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2950 (p : Pattern) (guard : d4207 p = 1) : d77 p ≤ (0 : Int) + d4221 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d77, d4221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2931 p hg
    simpa only [d77, d4221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d77, d4221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2949 p hg
    simpa only [d77, d4221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2951 (p : Pattern) (guard : d0 p = 1) : d400 p ≤ (0 : Int) + d4221 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2952 (p : Pattern) (guard : d4208 p = 1) : d517 p ≤ (0 : Int) + d4221 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2950 p hg
    simpa only [d4208, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2951 p hg
    simpa only [d4208, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2953 (p : Pattern) (guard : d1 p = 1) : d518 p ≤ (0 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d518, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d518, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d518, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d518, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2954 (p : Pattern) (guard : d4206 p = 1) : d519 p ≤ (0 : Int) + d15 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2953 p hg
    simpa only [d4206, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2911 p hg
    simpa only [d4206, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2955 (p : Pattern) (guard : d0 p = 1) : d59 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2956 (p : Pattern) (guard : d4206 p = 1) : d520 p ≤ (0 : Int) + d15 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2953 p hg
    simpa only [d4206, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2955 p hg
    simpa only [d4206, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2957 (p : Pattern) (guard : d4206 p = 1) : d521 p ≤ (0 : Int) + d15 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2954 p hg
    simpa only [d521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2956 p hg
    simpa only [d521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2958 (p : Pattern) (guard : d4206 p = 1) : d522 p ≤ (0 : Int) + d15 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2953 p hg
    simpa only [d4206, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2921 p hg
    simpa only [d4206, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2959 (p : Pattern) (guard : d1 p = 1) : d523 p ≤ (0 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d523, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d523, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d523, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1640 p hg
    simpa only [d523, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2960 (p : Pattern) (guard : d4206 p = 1) : d524 p ≤ (0 : Int) + d19 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2959 p hg
    simpa only [d4206, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2917 p hg
    simpa only [d4206, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2961 (p : Pattern) (guard : d4206 p = 1) : d525 p ≤ (0 : Int) + d4209 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d525, d4209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2958 p hg
    simpa only [d525, d4209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d525, d4209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2960 p hg
    simpa only [d525, d4209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2962 (p : Pattern) (guard : d4206 p = 1) : d526 p ≤ (0 : Int) + d4210 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d526, d4210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2957 p hg
    simpa only [d526, d4210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d526, d4210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2961 p hg
    simpa only [d526, d4210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2963 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (0 : Int) + d25 p := by
  omega
theorem compare2964 (p : Pattern) (guard : d4206 p = 1) : d527 p ≤ (0 : Int) + d25 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2963 p hg
    simpa only [d4206, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2925 p hg
    simpa only [d4206, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2965 (p : Pattern) (guard : d4206 p = 1) : d528 p ≤ (0 : Int) + d4211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d528, d4211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2964 p hg
    simpa only [d528, d4211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d528, d4211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d528, d4211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2966 (p : Pattern) (guard : d4206 p = 1) : d529 p ≤ (0 : Int) + d4212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d529, d4212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2961 p hg
    simpa only [d529, d4212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d529, d4212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2965 p hg
    simpa only [d529, d4212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2967 (p : Pattern) (guard : d4206 p = 1) : d530 p ≤ (0 : Int) + d4213 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d530, d4213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2962 p hg
    simpa only [d530, d4213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d530, d4213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2966 p hg
    simpa only [d530, d4213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2968 (p : Pattern) (guard : d4207 p = 1) : d531 p ≤ (0 : Int) + d4213 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2907 p hg
    simpa only [d4207, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2967 p hg
    simpa only [d4207, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2969 (p : Pattern) (guard : d1 p = 1) : d532 p ≤ (0 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d532, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d532, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d532, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare957 p hg
    simpa only [d532, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2970 (p : Pattern) (guard : d4206 p = 1) : d533 p ≤ (0 : Int) + d32 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2969 p hg
    simpa only [d4206, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2934 p hg
    simpa only [d4206, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2971 (p : Pattern) (guard : d4206 p = 1) : d534 p ≤ (0 : Int) + d4214 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d534, d4214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2956 p hg
    simpa only [d534, d4214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d534, d4214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2970 p hg
    simpa only [d534, d4214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2972 (p : Pattern) (guard : d4206 p = 1) : d535 p ≤ (0 : Int) + d4215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d535, d4215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2960 p hg
    simpa only [d535, d4215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d535, d4215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2964 p hg
    simpa only [d535, d4215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2973 (p : Pattern) (guard : d4206 p = 1) : d536 p ≤ (0 : Int) + d4216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d536, d4216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2971 p hg
    simpa only [d536, d4216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d536, d4216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2972 p hg
    simpa only [d536, d4216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2974 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (0 : Int) + d59 p := by
  omega
theorem compare2975 (p : Pattern) (guard : d4206 p = 1) : d277 p ≤ (0 : Int) + d59 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2974 p hg
    simpa only [d4206, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2940 p hg
    simpa only [d4206, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2976 (p : Pattern) (guard : d4206 p = 1) : d537 p ≤ (0 : Int) + d4217 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d537, d4217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2960 p hg
    simpa only [d537, d4217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d537, d4217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2975 p hg
    simpa only [d537, d4217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2977 (p : Pattern) (guard : d4206 p = 1) : d538 p ≤ (0 : Int) + d41 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d4206, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2944 p hg
    simpa only [d4206, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2978 (p : Pattern) (guard : d4206 p = 1) : d539 p ≤ (0 : Int) + d4218 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d539, d4218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2977 p hg
    simpa only [d539, d4218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d539, d4218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d539, d4218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2979 (p : Pattern) (guard : d4206 p = 1) : d540 p ≤ (0 : Int) + d4219 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d540, d4219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2976 p hg
    simpa only [d540, d4219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d540, d4219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2978 p hg
    simpa only [d540, d4219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2980 (p : Pattern) (guard : d4206 p = 1) : d541 p ≤ (0 : Int) + d4220 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d541, d4220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2973 p hg
    simpa only [d541, d4220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d541, d4220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2979 p hg
    simpa only [d541, d4220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2981 (p : Pattern) (guard : d4207 p = 1) : d542 p ≤ (0 : Int) + d4220 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2932 p hg
    simpa only [d4207, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2980 p hg
    simpa only [d4207, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2982 (p : Pattern) (guard : d4207 p = 1) : d543 p ≤ (0 : Int) + d4221 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d543, d4221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2968 p hg
    simpa only [d543, d4221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d543, d4221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2981 p hg
    simpa only [d543, d4221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2983 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d4227 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2984 (p : Pattern) (guard : d4208 p = 1) : d544 p ≤ (0 : Int) + d4228 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d544, d4228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2982 p hg
    simpa only [d4208, d544, d4228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d544, d4228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2983 p hg
    simpa only [d4208, d544, d4228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2985 (p : Pattern) (guard : d4208 p = 1) : d545 p ≤ (0 : Int) + d4229 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d545, d4229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2952 p hg
    simpa only [d545, d4229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d545, d4229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2984 p hg
    simpa only [d545, d4229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2986 (p : Pattern) (guard : d0 p = 1) : d422 p ≤ (0 : Int) + d4221 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2987 (p : Pattern) (guard : d4208 p = 1) : d546 p ≤ (0 : Int) + d4221 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2950 p hg
    simpa only [d4208, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2986 p hg
    simpa only [d4208, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2988 (p : Pattern) (guard : d4208 p = 1) : d547 p ≤ (0 : Int) + d4230 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d547, d4230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2982 p hg
    simpa only [d4208, d547, d4230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d547, d4230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4208, d547, d4230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2989 (p : Pattern) (guard : d4208 p = 1) : d548 p ≤ (0 : Int) + d4231 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d548, d4231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2987 p hg
    simpa only [d548, d4231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d548, d4231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2988 p hg
    simpa only [d548, d4231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2990 (p : Pattern) (guard : d4208 p = 1) : d549 p ≤ (0 : Int) + d4232 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d549, d4232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2985 p hg
    simpa only [d549, d4232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d549, d4232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2989 p hg
    simpa only [d549, d4232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2991 (p : Pattern) (guard : d0 p = 1) : d439 p ≤ (0 : Int) + d4221 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2992 (p : Pattern) (guard : d4208 p = 1) : d550 p ≤ (0 : Int) + d4221 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2950 p hg
    simpa only [d4208, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2991 p hg
    simpa only [d4208, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2993 (p : Pattern) (guard : d0 p = 1) : d441 p ≤ (0 : Int) + d4227 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2994 (p : Pattern) (guard : d4208 p = 1) : d551 p ≤ (0 : Int) + d4228 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d551, d4228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2982 p hg
    simpa only [d4208, d551, d4228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d551, d4228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2993 p hg
    simpa only [d4208, d551, d4228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2995 (p : Pattern) (guard : d4208 p = 1) : d552 p ≤ (0 : Int) + d4229 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d552, d4229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2992 p hg
    simpa only [d552, d4229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d552, d4229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2994 p hg
    simpa only [d552, d4229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2996 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d4221 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2997 (p : Pattern) (guard : d4208 p = 1) : d553 p ≤ (0 : Int) + d4221 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2950 p hg
    simpa only [d4208, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2996 p hg
    simpa only [d4208, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2998 (p : Pattern) (guard : d4208 p = 1) : d554 p ≤ (0 : Int) + d4231 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d554, d4231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2997 p hg
    simpa only [d554, d4231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d554, d4231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2988 p hg
    simpa only [d554, d4231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2999 (p : Pattern) (guard : d4208 p = 1) : d555 p ≤ (0 : Int) + d4232 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d555, d4232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2995 p hg
    simpa only [d555, d4232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d555, d4232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2998 p hg
    simpa only [d555, d4232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3000 (p : Pattern) (guard : d4208 p = 1) : d556 p ≤ (0 : Int) + d4232 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2990 p hg
    simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2999 p hg
    simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3001 (p : Pattern) (guard : d0 p = 1) : d114 p ≤ (0 : Int) + d4237 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3002 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1563 p hg
    simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3003 (p : Pattern) (guard : d0 p = 1) : d117 p ≤ (0 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3004 (p : Pattern) (guard : d4206 p = 1) : d118 p ≤ (0 : Int) + d104 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3002 p hg
    simpa only [d4206, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3003 p hg
    simpa only [d4206, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3005 (p : Pattern) (guard : d0 p = 1) : d121 p ≤ (0 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3006 (p : Pattern) (guard : d4206 p = 1) : d122 p ≤ (0 : Int) + d104 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3002 p hg
    simpa only [d4206, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3005 p hg
    simpa only [d4206, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3007 (p : Pattern) (guard : d4206 p = 1) : d123 p ≤ (0 : Int) + d104 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3004 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3006 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3008 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3009 (p : Pattern) (guard : d4206 p = 1) : d124 p ≤ (0 : Int) + d104 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3002 p hg
    simpa only [d4206, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3008 p hg
    simpa only [d4206, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3010 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1321 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3011 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d108 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3012 (p : Pattern) (guard : d4206 p = 1) : d125 p ≤ (0 : Int) + d108 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3010 p hg
    simpa only [d4206, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3011 p hg
    simpa only [d4206, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3013 (p : Pattern) (guard : d4206 p = 1) : d126 p ≤ (0 : Int) + d4233 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d126, d4233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3009 p hg
    simpa only [d126, d4233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d126, d4233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3012 p hg
    simpa only [d126, d4233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3014 (p : Pattern) (guard : d4206 p = 1) : d127 p ≤ (0 : Int) + d4234 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d127, d4234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3007 p hg
    simpa only [d127, d4234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d127, d4234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3013 p hg
    simpa only [d127, d4234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3015 (p : Pattern) (guard : d4206 p = 1) : d128 p ≤ (0 : Int) + d4235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d128, d4235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2941 p hg
    simpa only [d128, d4235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d128, d4235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d128, d4235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3016 (p : Pattern) (guard : d4206 p = 1) : d129 p ≤ (0 : Int) + d4236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d129, d4236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3013 p hg
    simpa only [d129, d4236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d129, d4236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3015 p hg
    simpa only [d129, d4236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3017 (p : Pattern) (guard : d4206 p = 1) : d130 p ≤ (0 : Int) + d4237 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d130, d4237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3014 p hg
    simpa only [d130, d4237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d130, d4237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3016 p hg
    simpa only [d130, d4237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3018 (p : Pattern) (guard : d4207 p = 1) : d131 p ≤ (0 : Int) + d4237 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3001 p hg
    simpa only [d4207, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3017 p hg
    simpa only [d4207, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3019 (p : Pattern) (guard : d0 p = 1) : d138 p ≤ (0 : Int) + d4243 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3020 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1573 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3021 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d117 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3022 (p : Pattern) (guard : d4206 p = 1) : d139 p ≤ (0 : Int) + d117 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3020 p hg
    simpa only [d4206, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3021 p hg
    simpa only [d4206, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3023 (p : Pattern) (guard : d4206 p = 1) : d140 p ≤ (0 : Int) + d4238 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d140, d4238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3006 p hg
    simpa only [d140, d4238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d140, d4238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3022 p hg
    simpa only [d140, d4238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3024 (p : Pattern) (guard : d4206 p = 1) : d141 p ≤ (0 : Int) + d4239 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d141, d4239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3012 p hg
    simpa only [d141, d4239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d141, d4239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2941 p hg
    simpa only [d141, d4239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3025 (p : Pattern) (guard : d4206 p = 1) : d142 p ≤ (0 : Int) + d4240 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d142, d4240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3023 p hg
    simpa only [d142, d4240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d142, d4240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3024 p hg
    simpa only [d142, d4240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3026 (p : Pattern) (guard : d4206 p = 1) : d143 p ≤ (0 : Int) + d4241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d143, d4241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3012 p hg
    simpa only [d143, d4241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d143, d4241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2945 p hg
    simpa only [d143, d4241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3027 (p : Pattern) (guard : d4206 p = 1) : d144 p ≤ (0 : Int) + d4242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d144, d4242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3026 p hg
    simpa only [d144, d4242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d144, d4242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d144, d4242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3028 (p : Pattern) (guard : d4206 p = 1) : d145 p ≤ (0 : Int) + d4243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d145, d4243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3025 p hg
    simpa only [d145, d4243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d145, d4243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3027 p hg
    simpa only [d145, d4243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3029 (p : Pattern) (guard : d4207 p = 1) : d146 p ≤ (0 : Int) + d4243 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3019 p hg
    simpa only [d4207, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3028 p hg
    simpa only [d4207, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3030 (p : Pattern) (guard : d4207 p = 1) : d147 p ≤ (0 : Int) + d4244 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d147, d4244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3018 p hg
    simpa only [d147, d4244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d147, d4244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3029 p hg
    simpa only [d147, d4244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3031 (p : Pattern) (guard : d0 p = 1) : d439 p ≤ (0 : Int) + d4244 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3032 (p : Pattern) (guard : d4208 p = 1) : d557 p ≤ (0 : Int) + d4244 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3030 p hg
    simpa only [d4208, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3031 p hg
    simpa only [d4208, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3033 (p : Pattern) (guard : d1 p = 1) : d558 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d558, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d558, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d558, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1321 p hg
    simpa only [d558, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3034 (p : Pattern) (guard : d4206 p = 1) : d559 p ≤ (0 : Int) + d104 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3033 p hg
    simpa only [d4206, d559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3005 p hg
    simpa only [d4206, d559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3035 (p : Pattern) (guard : d0 p = 1) : d41 p ≤ (0 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3036 (p : Pattern) (guard : d4206 p = 1) : d560 p ≤ (0 : Int) + d104 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3033 p hg
    simpa only [d4206, d560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3035 p hg
    simpa only [d4206, d560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3037 (p : Pattern) (guard : d4206 p = 1) : d561 p ≤ (0 : Int) + d104 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3034 p hg
    simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3036 p hg
    simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3038 (p : Pattern) (guard : d4206 p = 1) : d562 p ≤ (0 : Int) + d104 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3033 p hg
    simpa only [d4206, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3008 p hg
    simpa only [d4206, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3039 (p : Pattern) (guard : d1 p = 1) : d563 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d563, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d563, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d563, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d563, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3040 (p : Pattern) (guard : d4206 p = 1) : d564 p ≤ (0 : Int) + d108 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3039 p hg
    simpa only [d4206, d564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3011 p hg
    simpa only [d4206, d564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3041 (p : Pattern) (guard : d4206 p = 1) : d565 p ≤ (0 : Int) + d4233 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d565, d4233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3038 p hg
    simpa only [d565, d4233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d565, d4233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3040 p hg
    simpa only [d565, d4233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3042 (p : Pattern) (guard : d4206 p = 1) : d566 p ≤ (0 : Int) + d4234 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d566, d4234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3037 p hg
    simpa only [d566, d4234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d566, d4234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3041 p hg
    simpa only [d566, d4234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3043 (p : Pattern) (guard : d4206 p = 1) : d278 p ≤ (0 : Int) + d4235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d278, d4235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2975 p hg
    simpa only [d278, d4235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d278, d4235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d278, d4235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3044 (p : Pattern) (guard : d4206 p = 1) : d567 p ≤ (0 : Int) + d4236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d567, d4236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3041 p hg
    simpa only [d567, d4236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d567, d4236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3043 p hg
    simpa only [d567, d4236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3045 (p : Pattern) (guard : d4206 p = 1) : d568 p ≤ (0 : Int) + d4237 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d568, d4237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3042 p hg
    simpa only [d568, d4237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d568, d4237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3044 p hg
    simpa only [d568, d4237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3046 (p : Pattern) (guard : d4207 p = 1) : d569 p ≤ (0 : Int) + d4237 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3001 p hg
    simpa only [d4207, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3045 p hg
    simpa only [d4207, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3047 (p : Pattern) (guard : d1 p = 1) : d570 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d570, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d570, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d570, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d570, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3048 (p : Pattern) (guard : d4206 p = 1) : d571 p ≤ (0 : Int) + d117 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3047 p hg
    simpa only [d4206, d571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3021 p hg
    simpa only [d4206, d571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3049 (p : Pattern) (guard : d4206 p = 1) : d572 p ≤ (0 : Int) + d4238 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d572, d4238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3036 p hg
    simpa only [d572, d4238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d572, d4238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3048 p hg
    simpa only [d572, d4238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3050 (p : Pattern) (guard : d4206 p = 1) : d573 p ≤ (0 : Int) + d4239 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d573, d4239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3040 p hg
    simpa only [d573, d4239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d573, d4239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2975 p hg
    simpa only [d573, d4239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3051 (p : Pattern) (guard : d4206 p = 1) : d574 p ≤ (0 : Int) + d4240 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d574, d4240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3049 p hg
    simpa only [d574, d4240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d574, d4240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3050 p hg
    simpa only [d574, d4240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3052 (p : Pattern) (guard : d4206 p = 1) : d575 p ≤ (0 : Int) + d4241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d575, d4241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3040 p hg
    simpa only [d575, d4241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d575, d4241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2977 p hg
    simpa only [d575, d4241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3053 (p : Pattern) (guard : d4206 p = 1) : d576 p ≤ (0 : Int) + d4242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d576, d4242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3052 p hg
    simpa only [d576, d4242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d576, d4242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d576, d4242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3054 (p : Pattern) (guard : d4206 p = 1) : d577 p ≤ (0 : Int) + d4243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d577, d4243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3051 p hg
    simpa only [d577, d4243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d577, d4243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3053 p hg
    simpa only [d577, d4243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3055 (p : Pattern) (guard : d4207 p = 1) : d578 p ≤ (0 : Int) + d4243 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3019 p hg
    simpa only [d4207, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3054 p hg
    simpa only [d4207, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3056 (p : Pattern) (guard : d4207 p = 1) : d579 p ≤ (0 : Int) + d4244 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d579, d4244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3046 p hg
    simpa only [d579, d4244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d579, d4244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3055 p hg
    simpa only [d579, d4244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3057 (p : Pattern) (guard : d0 p = 1) : d441 p ≤ (0 : Int) + d4247 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3058 (p : Pattern) (guard : d4208 p = 1) : d580 p ≤ (0 : Int) + d4248 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d580, d4248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3056 p hg
    simpa only [d4208, d580, d4248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d580, d4248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3057 p hg
    simpa only [d4208, d580, d4248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3059 (p : Pattern) (guard : d4208 p = 1) : d581 p ≤ (0 : Int) + d4249 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d581, d4249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3032 p hg
    simpa only [d581, d4249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d581, d4249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3058 p hg
    simpa only [d581, d4249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3060 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d4244 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3061 (p : Pattern) (guard : d4208 p = 1) : d582 p ≤ (0 : Int) + d4244 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3030 p hg
    simpa only [d4208, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3060 p hg
    simpa only [d4208, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3062 (p : Pattern) (guard : d4208 p = 1) : d583 p ≤ (0 : Int) + d4250 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d583, d4250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3056 p hg
    simpa only [d4208, d583, d4250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d583, d4250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4208, d583, d4250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3063 (p : Pattern) (guard : d4208 p = 1) : d584 p ≤ (0 : Int) + d4251 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d584, d4251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3061 p hg
    simpa only [d584, d4251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d584, d4251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3062 p hg
    simpa only [d584, d4251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3064 (p : Pattern) (guard : d4208 p = 1) : d585 p ≤ (0 : Int) + d4252 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d585, d4252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3059 p hg
    simpa only [d585, d4252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d585, d4252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3063 p hg
    simpa only [d585, d4252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3065 (p : Pattern) (guard : d4208 p = 1) : d586 p ≤ (0 : Int) + d4253 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d586, d4253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2990 p hg
    simpa only [d586, d4253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d586, d4253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3064 p hg
    simpa only [d586, d4253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3066 (p : Pattern) (guard : d4208 p = 1) : d587 p ≤ (0 : Int) + d4254 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d587, d4254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3000 p hg
    simpa only [d587, d4254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d587, d4254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3065 p hg
    simpa only [d587, d4254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3067 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d4264 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3068 (p : Pattern) (guard : d4208 p = 1) : d553 p ≤ (0 : Int) + d4265 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d553, d4265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2950 p hg
    simpa only [d4208, d553, d4265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d553, d4265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3067 p hg
    simpa only [d4208, d553, d4265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3069 (p : Pattern) (guard : d0 p = 1) : d189 p ≤ (0 : Int) + d4258 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3070 (p : Pattern) (guard : d1 p = 1) : d588 p ≤ (0 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d588, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d588, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d588, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d588, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3071 (p : Pattern) (guard : d4206 p = 1) : d589 p ≤ (0 : Int) + d32 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3070 p hg
    simpa only [d4206, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2934 p hg
    simpa only [d4206, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3072 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (0 : Int) + d35 p := by
  omega
theorem compare3073 (p : Pattern) (guard : d1 p = 1) : d590 p ≤ (0 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d590, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d590, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d590, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1640 p hg
    simpa only [d590, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3074 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d36 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3075 (p : Pattern) (guard : d4206 p = 1) : d591 p ≤ (0 : Int) + d36 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3073 p hg
    simpa only [d4206, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3074 p hg
    simpa only [d4206, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3076 (p : Pattern) (guard : d4206 p = 1) : d592 p ≤ (0 : Int) + d4255 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d592, d4255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3071 p hg
    simpa only [d592, d4255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d592, d4255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3075 p hg
    simpa only [d592, d4255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3077 (p : Pattern) (guard : d4206 p = 1) : d593 p ≤ (0 : Int) + d4256 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d593, d4256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2957 p hg
    simpa only [d593, d4256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d593, d4256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3076 p hg
    simpa only [d593, d4256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3078 (p : Pattern) (guard : d4206 p = 1) : d594 p ≤ (0 : Int) + d4257 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d594, d4257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3076 p hg
    simpa only [d594, d4257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d594, d4257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2978 p hg
    simpa only [d594, d4257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3079 (p : Pattern) (guard : d4206 p = 1) : d595 p ≤ (0 : Int) + d4258 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d595, d4258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3077 p hg
    simpa only [d595, d4258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d595, d4258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3078 p hg
    simpa only [d595, d4258, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
