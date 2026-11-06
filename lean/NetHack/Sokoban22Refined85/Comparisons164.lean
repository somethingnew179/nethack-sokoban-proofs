/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons163
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare22960 (p : Pattern) (guard : d0 p = 1) : d2504 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22961 (p : Pattern) (guard : d5503 p = 1) : d2505 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21088 p hg
    simpa only [d5503, d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22960 p hg
    simpa only [d5503, d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22962 (p : Pattern) (guard : d0 p = 1) : d2506 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22963 (p : Pattern) (guard : d5503 p = 1) : d2507 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d5503, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22962 p hg
    simpa only [d5503, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22964 (p : Pattern) (guard : d5503 p = 1) : d2508 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22961 p hg
    simpa only [d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22963 p hg
    simpa only [d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22965 (p : Pattern) (guard : d0 p = 1) : d2509 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22966 (p : Pattern) (guard : d5503 p = 1) : d2510 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d5503, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22965 p hg
    simpa only [d5503, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22967 (p : Pattern) (guard : d5503 p = 1) : d2511 p ≤ (0 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2511, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22966 p hg
    simpa only [d2511, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2511, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2511, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22968 (p : Pattern) (guard : d5503 p = 1) : d2512 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2512, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22964 p hg
    simpa only [d2512, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2512, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22967 p hg
    simpa only [d2512, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22969 (p : Pattern) (guard : d5503 p = 1) : d2514 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21102 p hg
    simpa only [d5503, d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22960 p hg
    simpa only [d5503, d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22970 (p : Pattern) (guard : d5503 p = 1) : d2515 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22969 p hg
    simpa only [d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22963 p hg
    simpa only [d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22971 (p : Pattern) (guard : d5503 p = 1) : d2516 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2516, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22970 p hg
    simpa only [d2516, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2516, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22967 p hg
    simpa only [d2516, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22972 (p : Pattern) (guard : d5503 p = 1) : d2517 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22968 p hg
    simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22971 p hg
    simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22973 (p : Pattern) (guard : d5503 p = 1) : d2504 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22960 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22974 (p : Pattern) (guard : d5503 p = 1) : d2518 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22973 p hg
    simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22963 p hg
    simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22975 (p : Pattern) (guard : d5503 p = 1) : d2519 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2519, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22974 p hg
    simpa only [d2519, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2519, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22967 p hg
    simpa only [d2519, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22976 (p : Pattern) (guard : d0 p = 1) : d2520 p ≤ (0 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22977 (p : Pattern) (guard : d5503 p = 1) : d2520 p ≤ (0 : Int) + d18 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21109 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22976 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22978 (p : Pattern) (guard : d0 p = 1) : d2521 p ≤ (0 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22979 (p : Pattern) (guard : d5503 p = 1) : d2522 p ≤ (0 : Int) + d18 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21109 p hg
    simpa only [d5503, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22978 p hg
    simpa only [d5503, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22980 (p : Pattern) (guard : d5503 p = 1) : d2523 p ≤ (0 : Int) + d18 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22977 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22979 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22981 (p : Pattern) (guard : d0 p = 1) : d2524 p ≤ (0 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22982 (p : Pattern) (guard : d5503 p = 1) : d2525 p ≤ (0 : Int) + d18 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21109 p hg
    simpa only [d5503, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22981 p hg
    simpa only [d5503, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22983 (p : Pattern) (guard : d5503 p = 1) : d2526 p ≤ (0 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2526, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22982 p hg
    simpa only [d2526, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2526, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2526, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22984 (p : Pattern) (guard : d5503 p = 1) : d2527 p ≤ (0 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2527, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22980 p hg
    simpa only [d2527, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2527, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22983 p hg
    simpa only [d2527, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22985 (p : Pattern) (guard : d5503 p = 1) : d2528 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2528, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22975 p hg
    simpa only [d2528, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2528, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22984 p hg
    simpa only [d2528, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22986 (p : Pattern) (guard : d5503 p = 1) : d2529 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2529, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22972 p hg
    simpa only [d2529, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2529, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22985 p hg
    simpa only [d2529, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22987 (p : Pattern) (guard : d0 p = 1) : d2530 p ≤ (0 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22988 (p : Pattern) (guard : d5503 p = 1) : d2530 p ≤ (0 : Int) + d24 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21121 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22987 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22989 (p : Pattern) (guard : d0 p = 1) : d357 p ≤ (0 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22990 (p : Pattern) (guard : d5503 p = 1) : d2531 p ≤ (0 : Int) + d24 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21121 p hg
    simpa only [d5503, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22989 p hg
    simpa only [d5503, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22991 (p : Pattern) (guard : d5503 p = 1) : d2532 p ≤ (0 : Int) + d24 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22988 p hg
    simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22990 p hg
    simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22992 (p : Pattern) (guard : d0 p = 1) : d2533 p ≤ (0 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22993 (p : Pattern) (guard : d5503 p = 1) : d2534 p ≤ (0 : Int) + d24 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21121 p hg
    simpa only [d5503, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22992 p hg
    simpa only [d5503, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22994 (p : Pattern) (guard : d5503 p = 1) : d2535 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2535, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22993 p hg
    simpa only [d2535, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2535, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2535, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22995 (p : Pattern) (guard : d5503 p = 1) : d2536 p ≤ (0 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2536, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22991 p hg
    simpa only [d2536, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2536, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22994 p hg
    simpa only [d2536, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22996 (p : Pattern) (guard : d5503 p = 1) : d2537 p ≤ (0 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2537, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22995 p hg
    simpa only [d2537, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2537, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2537, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22997 (p : Pattern) (guard : d5503 p = 1) : d2538 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2538, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22985 p hg
    simpa only [d2538, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2538, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22996 p hg
    simpa only [d2538, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22998 (p : Pattern) (guard : d5503 p = 1) : d2539 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2539, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22986 p hg
    simpa only [d2539, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2539, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22997 p hg
    simpa only [d2539, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22999 (p : Pattern) (guard : d0 p = 1) : d2541 p ≤ (0 : Int) + d31 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23000 (p : Pattern) (guard : d5503 p = 1) : d2542 p ≤ (0 : Int) + d31 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21177 p hg
    simpa only [d5503, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22999 p hg
    simpa only [d5503, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23001 (p : Pattern) (guard : d5503 p = 1) : d2543 p ≤ (0 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2543, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23000 p hg
    simpa only [d2543, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2543, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2543, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23002 (p : Pattern) (guard : d5503 p = 1) : d2544 p ≤ (0 : Int) + d33 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2544, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22974 p hg
    simpa only [d2544, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2544, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23001 p hg
    simpa only [d2544, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23003 (p : Pattern) (guard : d0 p = 1) : d2546 p ≤ (0 : Int) + d35 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23004 (p : Pattern) (guard : d5503 p = 1) : d2547 p ≤ (0 : Int) + d35 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21244 p hg
    simpa only [d5503, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23003 p hg
    simpa only [d5503, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23005 (p : Pattern) (guard : d5503 p = 1) : d2548 p ≤ (0 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2548, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23004 p hg
    simpa only [d2548, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2548, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2548, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23006 (p : Pattern) (guard : d5503 p = 1) : d2549 p ≤ (0 : Int) + d37 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2549, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22974 p hg
    simpa only [d2549, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2549, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23005 p hg
    simpa only [d2549, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23007 (p : Pattern) (guard : d5503 p = 1) : d2550 p ≤ (0 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2550, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23002 p hg
    simpa only [d2550, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2550, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23006 p hg
    simpa only [d2550, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23008 (p : Pattern) (guard : d0 p = 1) : d332 p ≤ (0 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23009 (p : Pattern) (guard : d5503 p = 1) : d2552 p ≤ (0 : Int) + d40 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21198 p hg
    simpa only [d5503, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23008 p hg
    simpa only [d5503, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23010 (p : Pattern) (guard : d5503 p = 1) : d2553 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2553, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23009 p hg
    simpa only [d2553, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2553, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2553, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23011 (p : Pattern) (guard : d5503 p = 1) : d2554 p ≤ (0 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2554, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22974 p hg
    simpa only [d2554, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2554, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23010 p hg
    simpa only [d2554, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23012 (p : Pattern) (guard : d5503 p = 1) : d2555 p ≤ (0 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2555, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22980 p hg
    simpa only [d2555, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2555, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2555, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23013 (p : Pattern) (guard : d5503 p = 1) : d2556 p ≤ (0 : Int) + d44 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2556, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23011 p hg
    simpa only [d2556, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2556, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23012 p hg
    simpa only [d2556, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23014 (p : Pattern) (guard : d5503 p = 1) : d2557 p ≤ (0 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2557, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23007 p hg
    simpa only [d2557, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2557, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23013 p hg
    simpa only [d2557, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23015 (p : Pattern) (guard : d5503 p = 1) : d2558 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2558, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22974 p hg
    simpa only [d2558, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2558, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2558, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23016 (p : Pattern) (guard : d5503 p = 1) : d2559 p ≤ (0 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2559, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23015 p hg
    simpa only [d2559, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2559, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23012 p hg
    simpa only [d2559, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23017 (p : Pattern) (guard : d5503 p = 1) : d2560 p ≤ (0 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2560, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22991 p hg
    simpa only [d2560, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2560, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2560, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23018 (p : Pattern) (guard : d5503 p = 1) : d2561 p ≤ (0 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2561, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23017 p hg
    simpa only [d2561, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2561, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2561, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23019 (p : Pattern) (guard : d5503 p = 1) : d2562 p ≤ (0 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2562, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23016 p hg
    simpa only [d2562, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2562, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23018 p hg
    simpa only [d2562, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23020 (p : Pattern) (guard : d5503 p = 1) : d2563 p ≤ (0 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2563, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23014 p hg
    simpa only [d2563, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2563, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23019 p hg
    simpa only [d2563, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23021 (p : Pattern) (guard : d5503 p = 1) : d2564 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2564, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22998 p hg
    simpa only [d2564, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2564, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23020 p hg
    simpa only [d2564, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23022 (p : Pattern) (guard : d5503 p = 1) : d2566 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21173 p hg
    simpa only [d5503, d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22960 p hg
    simpa only [d5503, d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23023 (p : Pattern) (guard : d5503 p = 1) : d2567 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23022 p hg
    simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22963 p hg
    simpa only [d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23024 (p : Pattern) (guard : d5503 p = 1) : d2568 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2568, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23023 p hg
    simpa only [d2568, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2568, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22967 p hg
    simpa only [d2568, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23025 (p : Pattern) (guard : d0 p = 1) : d2540 p ≤ (0 : Int) + d31 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23026 (p : Pattern) (guard : d5503 p = 1) : d2540 p ≤ (0 : Int) + d31 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21177 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23025 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23027 (p : Pattern) (guard : d5503 p = 1) : d2569 p ≤ (0 : Int) + d31 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23026 p hg
    simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23000 p hg
    simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23028 (p : Pattern) (guard : d0 p = 1) : d2570 p ≤ (0 : Int) + d31 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23029 (p : Pattern) (guard : d5503 p = 1) : d2571 p ≤ (0 : Int) + d31 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21177 p hg
    simpa only [d5503, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23028 p hg
    simpa only [d5503, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23030 (p : Pattern) (guard : d5503 p = 1) : d2572 p ≤ (0 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2572, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23029 p hg
    simpa only [d2572, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2572, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2572, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23031 (p : Pattern) (guard : d5503 p = 1) : d2573 p ≤ (0 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2573, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23027 p hg
    simpa only [d2573, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2573, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23030 p hg
    simpa only [d2573, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23032 (p : Pattern) (guard : d5503 p = 1) : d2574 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2574, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23024 p hg
    simpa only [d2574, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2574, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23031 p hg
    simpa only [d2574, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23033 (p : Pattern) (guard : d5503 p = 1) : d2575 p ≤ (0 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2575, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22984 p hg
    simpa only [d2575, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2575, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22995 p hg
    simpa only [d2575, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23034 (p : Pattern) (guard : d5503 p = 1) : d2576 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2576, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23032 p hg
    simpa only [d2576, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2576, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23033 p hg
    simpa only [d2576, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23035 (p : Pattern) (guard : d0 p = 1) : d2577 p ≤ (0 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23036 (p : Pattern) (guard : d5503 p = 1) : d2577 p ≤ (0 : Int) + d58 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21190 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23035 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23037 (p : Pattern) (guard : d0 p = 1) : d330 p ≤ (0 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23038 (p : Pattern) (guard : d5503 p = 1) : d2578 p ≤ (0 : Int) + d58 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21190 p hg
    simpa only [d5503, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23037 p hg
    simpa only [d5503, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23039 (p : Pattern) (guard : d5503 p = 1) : d2579 p ≤ (0 : Int) + d58 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23036 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23038 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23040 (p : Pattern) (guard : d5503 p = 1) : d2580 p ≤ (0 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2580, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23038 p hg
    simpa only [d2580, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2580, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2580, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23041 (p : Pattern) (guard : d5503 p = 1) : d2581 p ≤ (0 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2581, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23039 p hg
    simpa only [d2581, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2581, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23040 p hg
    simpa only [d2581, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23042 (p : Pattern) (guard : d5503 p = 1) : d2582 p ≤ (0 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2582, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22984 p hg
    simpa only [d2582, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2582, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23041 p hg
    simpa only [d2582, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23043 (p : Pattern) (guard : d0 p = 1) : d2551 p ≤ (0 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23044 (p : Pattern) (guard : d5503 p = 1) : d2551 p ≤ (0 : Int) + d40 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21198 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23043 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23045 (p : Pattern) (guard : d5503 p = 1) : d2583 p ≤ (0 : Int) + d40 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23044 p hg
    simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23009 p hg
    simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23046 (p : Pattern) (guard : d5503 p = 1) : d2584 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2584, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23045 p hg
    simpa only [d2584, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2584, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23010 p hg
    simpa only [d2584, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23047 (p : Pattern) (guard : d5503 p = 1) : d2585 p ≤ (0 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2585, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23046 p hg
    simpa only [d2585, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2585, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2585, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23048 (p : Pattern) (guard : d5503 p = 1) : d2586 p ≤ (0 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2586, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23042 p hg
    simpa only [d2586, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2586, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23047 p hg
    simpa only [d2586, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23049 (p : Pattern) (guard : d5503 p = 1) : d2587 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2587, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23034 p hg
    simpa only [d2587, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2587, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23048 p hg
    simpa only [d2587, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23050 (p : Pattern) (guard : d5503 p = 1) : d2588 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2588, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23027 p hg
    simpa only [d2588, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2588, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2588, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23051 (p : Pattern) (guard : d5503 p = 1) : d2589 p ≤ (0 : Int) + d67 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2589, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23006 p hg
    simpa only [d2589, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2589, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23050 p hg
    simpa only [d2589, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23052 (p : Pattern) (guard : d5503 p = 1) : d2590 p ≤ (0 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2590, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23012 p hg
    simpa only [d2590, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2590, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23017 p hg
    simpa only [d2590, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23053 (p : Pattern) (guard : d5503 p = 1) : d2591 p ≤ (0 : Int) + d69 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2591, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23051 p hg
    simpa only [d2591, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2591, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23052 p hg
    simpa only [d2591, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23054 (p : Pattern) (guard : d5503 p = 1) : d2592 p ≤ (0 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2592, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23039 p hg
    simpa only [d2592, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2592, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2592, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23055 (p : Pattern) (guard : d5503 p = 1) : d2593 p ≤ (0 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2593, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23012 p hg
    simpa only [d2593, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2593, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23054 p hg
    simpa only [d2593, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23056 (p : Pattern) (guard : d5503 p = 1) : d2594 p ≤ (0 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2594, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23045 p hg
    simpa only [d2594, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2594, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2594, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23057 (p : Pattern) (guard : d5503 p = 1) : d2595 p ≤ (0 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2595, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23056 p hg
    simpa only [d2595, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2595, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2595, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23058 (p : Pattern) (guard : d5503 p = 1) : d2596 p ≤ (0 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2596, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23055 p hg
    simpa only [d2596, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2596, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23057 p hg
    simpa only [d2596, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23059 (p : Pattern) (guard : d5503 p = 1) : d2597 p ≤ (0 : Int) + d75 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2597, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23053 p hg
    simpa only [d2597, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2597, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23058 p hg
    simpa only [d2597, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23060 (p : Pattern) (guard : d5503 p = 1) : d2598 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2598, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23049 p hg
    simpa only [d2598, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2598, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23059 p hg
    simpa only [d2598, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23061 (p : Pattern) (guard : d5503 p = 1) : d2599 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2599, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23021 p hg
    simpa only [d2599, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2599, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23060 p hg
    simpa only [d2599, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23062 (p : Pattern) (guard : d5503 p = 1) : d2600 p ≤ (0 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2600, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22963 p hg
    simpa only [d2600, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2600, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2600, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23063 (p : Pattern) (guard : d5503 p = 1) : d2601 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2601, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22974 p hg
    simpa only [d2601, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2601, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23062 p hg
    simpa only [d2601, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23064 (p : Pattern) (guard : d5503 p = 1) : d2602 p ≤ (0 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2602, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22979 p hg
    simpa only [d2602, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2602, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2602, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23065 (p : Pattern) (guard : d5503 p = 1) : d2603 p ≤ (0 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2603, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22980 p hg
    simpa only [d2603, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2603, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23064 p hg
    simpa only [d2603, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23066 (p : Pattern) (guard : d5503 p = 1) : d2604 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2604, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23063 p hg
    simpa only [d2604, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2604, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23065 p hg
    simpa only [d2604, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23067 (p : Pattern) (guard : d5503 p = 1) : d2605 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2605, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23063 p hg
    simpa only [d2605, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2605, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23066 p hg
    simpa only [d2605, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23068 (p : Pattern) (guard : d5503 p = 1) : d2606 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2606, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22990 p hg
    simpa only [d2606, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2606, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2606, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23069 (p : Pattern) (guard : d5503 p = 1) : d2607 p ≤ (0 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2607, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22991 p hg
    simpa only [d2607, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2607, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23068 p hg
    simpa only [d2607, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23070 (p : Pattern) (guard : d5503 p = 1) : d2608 p ≤ (0 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2608, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23069 p hg
    simpa only [d2608, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2608, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2608, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23071 (p : Pattern) (guard : d5503 p = 1) : d2609 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2609, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23066 p hg
    simpa only [d2609, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2609, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23070 p hg
    simpa only [d2609, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23072 (p : Pattern) (guard : d5503 p = 1) : d2610 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2610, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23067 p hg
    simpa only [d2610, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2610, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23071 p hg
    simpa only [d2610, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23073 (p : Pattern) (guard : d5503 p = 1) : d2611 p ≤ (0 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2611, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23027 p hg
    simpa only [d2611, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2611, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23001 p hg
    simpa only [d2611, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23074 (p : Pattern) (guard : d0 p = 1) : d2545 p ≤ (0 : Int) + d35 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23075 (p : Pattern) (guard : d5503 p = 1) : d2545 p ≤ (0 : Int) + d35 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21244 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23074 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23076 (p : Pattern) (guard : d5503 p = 1) : d2612 p ≤ (0 : Int) + d35 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23075 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23004 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23077 (p : Pattern) (guard : d5503 p = 1) : d2613 p ≤ (0 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2613, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23076 p hg
    simpa only [d2613, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2613, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23005 p hg
    simpa only [d2613, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23078 (p : Pattern) (guard : d5503 p = 1) : d2614 p ≤ (0 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2614, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23073 p hg
    simpa only [d2614, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2614, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23077 p hg
    simpa only [d2614, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23079 (p : Pattern) (guard : d5503 p = 1) : d2615 p ≤ (0 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2615, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23078 p hg
    simpa only [d2615, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2615, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23047 p hg
    simpa only [d2615, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23080 (p : Pattern) (guard : d5503 p = 1) : d2616 p ≤ (0 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2616, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23079 p hg
    simpa only [d2616, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2616, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2616, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23081 (p : Pattern) (guard : d5503 p = 1) : d2617 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2617, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23072 p hg
    simpa only [d2617, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2617, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23080 p hg
    simpa only [d2617, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23082 (p : Pattern) (guard : d5503 p = 1) : d2618 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2618, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23063 p hg
    simpa only [d2618, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2618, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23073 p hg
    simpa only [d2618, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23083 (p : Pattern) (guard : d5503 p = 1) : d2619 p ≤ (0 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2619, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23065 p hg
    simpa only [d2619, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2619, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23069 p hg
    simpa only [d2619, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23084 (p : Pattern) (guard : d5503 p = 1) : d2620 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2620, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23082 p hg
    simpa only [d2620, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2620, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23083 p hg
    simpa only [d2620, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23085 (p : Pattern) (guard : d5503 p = 1) : d2621 p ≤ (0 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2621, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23065 p hg
    simpa only [d2621, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2621, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23041 p hg
    simpa only [d2621, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23086 (p : Pattern) (guard : d5503 p = 1) : d2622 p ≤ (0 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2622, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23085 p hg
    simpa only [d2622, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2622, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23047 p hg
    simpa only [d2622, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23087 (p : Pattern) (guard : d5503 p = 1) : d2623 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2623, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23084 p hg
    simpa only [d2623, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2623, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23086 p hg
    simpa only [d2623, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23088 (p : Pattern) (guard : d5503 p = 1) : d2624 p ≤ (0 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2624, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23077 p hg
    simpa only [d2624, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2624, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2624, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23089 (p : Pattern) (guard : d5503 p = 1) : d2625 p ≤ (0 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2625, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23088 p hg
    simpa only [d2625, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2625, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2625, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23090 (p : Pattern) (guard : d5503 p = 1) : d2626 p ≤ (0 : Int) + d85 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2626, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23089 p hg
    simpa only [d2626, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2626, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2626, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23091 (p : Pattern) (guard : d5503 p = 1) : d2627 p ≤ (0 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2627, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23087 p hg
    simpa only [d2627, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2627, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23090 p hg
    simpa only [d2627, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23092 (p : Pattern) (guard : d5503 p = 1) : d2628 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2628, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23081 p hg
    simpa only [d2628, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2628, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23091 p hg
    simpa only [d2628, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23093 (p : Pattern) (guard : d5503 p = 1) : d2629 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2629, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23061 p hg
    simpa only [d2629, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2629, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23092 p hg
    simpa only [d2629, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23094 (p : Pattern) (guard : d5503 p = 1) : d2630 p ≤ (0 : Int) + d89 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2630, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23069 p hg
    simpa only [d2630, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2630, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23046 p hg
    simpa only [d2630, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23095 (p : Pattern) (guard : d5503 p = 1) : d2631 p ≤ (0 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2631, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23094 p hg
    simpa only [d2631, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2631, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23047 p hg
    simpa only [d2631, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23096 (p : Pattern) (guard : d5503 p = 1) : d2632 p ≤ (0 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2632, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23047 p hg
    simpa only [d2632, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2632, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2632, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23097 (p : Pattern) (guard : d5503 p = 1) : d2633 p ≤ (0 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2633, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23095 p hg
    simpa only [d2633, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2633, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23096 p hg
    simpa only [d2633, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23098 (p : Pattern) (guard : d5503 p = 1) : d2634 p ≤ (0 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2634, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23096 p hg
    simpa only [d2634, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2634, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2634, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23099 (p : Pattern) (guard : d5503 p = 1) : d2635 p ≤ (0 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2635, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23097 p hg
    simpa only [d2635, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2635, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23098 p hg
    simpa only [d2635, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
