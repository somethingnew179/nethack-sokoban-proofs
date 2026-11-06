/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons228
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare32060 (p : Pattern) (guard : d5849 p = 1) : d4008 p ≤ (0 : Int) + d2479 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4008, d2479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32059 p hg
    simpa only [d4008, d2479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4008, d2479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31892 p hg
    simpa only [d4008, d2479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32061 (p : Pattern) (guard : d0 p = 1) : d4009 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32062 (p : Pattern) (guard : d5849 p = 1) : d4010 p ≤ (0 : Int) + d2336 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d4010, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31796 p hg
    simpa only [d5849, d4010, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d4010, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32061 p hg
    simpa only [d5849, d4010, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32063 (p : Pattern) (guard : d5849 p = 1) : d4011 p ≤ (0 : Int) + d2337 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4011, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32062 p hg
    simpa only [d4011, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4011, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d4011, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32064 (p : Pattern) (guard : d5849 p = 1) : d4012 p ≤ (0 : Int) + d2354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4012, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31846 p hg
    simpa only [d4012, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4012, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32063 p hg
    simpa only [d4012, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32065 (p : Pattern) (guard : d5849 p = 1) : d4013 p ≤ (0 : Int) + d2354 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32064 p hg
    simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31874 p hg
    simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32066 (p : Pattern) (guard : d5849 p = 1) : d4014 p ≤ (0 : Int) + d2480 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4014, d2480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d4014, d2480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4014, d2480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32003 p hg
    simpa only [d4014, d2480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32067 (p : Pattern) (guard : d5849 p = 1) : d4015 p ≤ (0 : Int) + d2481 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4015, d2481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32066 p hg
    simpa only [d4015, d2481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4015, d2481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31891 p hg
    simpa only [d4015, d2481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32068 (p : Pattern) (guard : d5849 p = 1) : d4016 p ≤ (0 : Int) + d2482 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4016, d2482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31664 p hg
    simpa only [d4016, d2482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4016, d2482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d4016, d2482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32069 (p : Pattern) (guard : d5849 p = 1) : d4017 p ≤ (0 : Int) + d2483 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4017, d2483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32068 p hg
    simpa only [d4017, d2483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4017, d2483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d4017, d2483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32070 (p : Pattern) (guard : d5849 p = 1) : d4018 p ≤ (0 : Int) + d2484 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4018, d2484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32067 p hg
    simpa only [d4018, d2484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4018, d2484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32069 p hg
    simpa only [d4018, d2484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32071 (p : Pattern) (guard : d5849 p = 1) : d4019 p ≤ (0 : Int) + d2485 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4019, d2485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32060 p hg
    simpa only [d4019, d2485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4019, d2485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32070 p hg
    simpa only [d4019, d2485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32072 (p : Pattern) (guard : d5849 p = 1) : d4020 p ≤ (0 : Int) + d2486 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4020, d2486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32055 p hg
    simpa only [d4020, d2486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4020, d2486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32071 p hg
    simpa only [d4020, d2486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32073 (p : Pattern) (guard : d5849 p = 1) : d4021 p ≤ (0 : Int) + d2487 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4021, d2487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31874 p hg
    simpa only [d4021, d2487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4021, d2487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31663 p hg
    simpa only [d4021, d2487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32074 (p : Pattern) (guard : d5849 p = 1) : d4022 p ≤ (0 : Int) + d2488 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4022, d2488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32056 p hg
    simpa only [d4022, d2488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4022, d2488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32073 p hg
    simpa only [d4022, d2488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32075 (p : Pattern) (guard : d5849 p = 1) : d4023 p ≤ (0 : Int) + d2489 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4023, d2489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31869 p hg
    simpa only [d4023, d2489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4023, d2489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31663 p hg
    simpa only [d4023, d2489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32076 (p : Pattern) (guard : d5849 p = 1) : d4024 p ≤ (0 : Int) + d2490 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4024, d2490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d4024, d2490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4024, d2490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d4024, d2490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32077 (p : Pattern) (guard : d5849 p = 1) : d4025 p ≤ (0 : Int) + d2491 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4025, d2491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32074 p hg
    simpa only [d4025, d2491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4025, d2491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32076 p hg
    simpa only [d4025, d2491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32078 (p : Pattern) (guard : d5849 p = 1) : d4026 p ≤ (0 : Int) + d2492 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4026, d2492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31879 p hg
    simpa only [d4026, d2492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4026, d2492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31629 p hg
    simpa only [d4026, d2492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32079 (p : Pattern) (guard : d5849 p = 1) : d4027 p ≤ (0 : Int) + d2493 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4027, d2493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32078 p hg
    simpa only [d4027, d2493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4027, d2493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d4027, d2493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32080 (p : Pattern) (guard : d5849 p = 1) : d4028 p ≤ (0 : Int) + d2494 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4028, d2494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32079 p hg
    simpa only [d4028, d2494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4028, d2494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d4028, d2494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32081 (p : Pattern) (guard : d5849 p = 1) : d4029 p ≤ (0 : Int) + d2495 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4029, d2495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32077 p hg
    simpa only [d4029, d2495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4029, d2495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32080 p hg
    simpa only [d4029, d2495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32082 (p : Pattern) (guard : d5849 p = 1) : d4030 p ≤ (0 : Int) + d2496 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4030, d2496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32081 p hg
    simpa only [d4030, d2496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4030, d2496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32070 p hg
    simpa only [d4030, d2496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32083 (p : Pattern) (guard : d5849 p = 1) : d4031 p ≤ (0 : Int) + d2497 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4031, d2497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32082 p hg
    simpa only [d4031, d2497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4031, d2497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d4031, d2497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32084 (p : Pattern) (guard : d5849 p = 1) : d4032 p ≤ (0 : Int) + d2498 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4032, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32072 p hg
    simpa only [d4032, d2498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4032, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32083 p hg
    simpa only [d4032, d2498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32085 (p : Pattern) (guard : d5849 p = 1) : d4033 p ≤ (0 : Int) + d2499 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4033, d2499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32011 p hg
    simpa only [d4033, d2499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4033, d2499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32084 p hg
    simpa only [d4033, d2499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32086 (p : Pattern) (guard : d5849 p = 1) : d4034 p ≤ (0 : Int) + d2500 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4034, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31718 p hg
    simpa only [d4034, d2500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4034, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32085 p hg
    simpa only [d4034, d2500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32087 (p : Pattern) (guard : d5849 p = 1) : d4035 p ≤ (0 : Int) + d2501 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4035, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31992 p hg
    simpa only [d4035, d2501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4035, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32086 p hg
    simpa only [d4035, d2501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32088 (p : Pattern) (guard : d5849 p = 1) : d4036 p ≤ (0 : Int) + d2502 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4036, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31916 p hg
    simpa only [d4036, d2502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4036, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32087 p hg
    simpa only [d4036, d2502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32089 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d1769 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15669 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4694 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32090 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d1770 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32089 p hg
    simpa only [d14, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4695 p hg
    simpa only [d14, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32091 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d1771 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32090 p hg
    simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32092 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d1772 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32091 p hg
    simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32090 p hg
    simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32093 (p : Pattern) (guard : d0 p = 1) : d1772 p ≤ (2 : Int) + d1772 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32094 (p : Pattern) (guard : d4474 p = 1) : d2895 p ≤ (2 : Int) + d1772 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32092 p hg
    simpa only [d4474, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32093 p hg
    simpa only [d4474, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32095 (p : Pattern) (guard : d1 p = 1) : d1683 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15806 p hg
    simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12151 p hg
    simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32096 (p : Pattern) (guard : d1 p = 1) : d1684 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32095 p hg
    simpa only [d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12152 p hg
    simpa only [d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32097 (p : Pattern) (guard : d1 p = 1) : d1685 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15808 p hg
    simpa only [d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32096 p hg
    simpa only [d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32098 (p : Pattern) (guard : d1 p = 1) : d1686 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32096 p hg
    simpa only [d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32099 (p : Pattern) (guard : d4474 p = 1) : d1687 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d4474, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32100 (p : Pattern) (guard : d4474 p = 1) : d2896 p ≤ (2 : Int) + d7014 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2896, d7014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32094 p hg
    simpa only [d2896, d7014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2896, d7014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32099 p hg
    simpa only [d2896, d7014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32101 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d1794 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15683 p hg
    simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16120 p hg
    simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32102 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d1795 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d18, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16122 p hg
    simpa only [d18, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32103 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d2011 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7129 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32104 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d2012 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32105 (p : Pattern) (guard : d0 p = 1) : d2012 p ≤ (2 : Int) + d2012 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32106 (p : Pattern) (guard : d4474 p = 1) : d2897 p ≤ (2 : Int) + d2012 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32104 p hg
    simpa only [d4474, d2897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32105 p hg
    simpa only [d4474, d2897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32107 (p : Pattern) (guard : d1 p = 1) : d1693 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4711 p hg
    simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4840 p hg
    simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32108 (p : Pattern) (guard : d1 p = 1) : d1694 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32107 p hg
    simpa only [d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4841 p hg
    simpa only [d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32109 (p : Pattern) (guard : d1 p = 1) : d1695 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4713 p hg
    simpa only [d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32108 p hg
    simpa only [d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32110 (p : Pattern) (guard : d1 p = 1) : d1696 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32109 p hg
    simpa only [d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32108 p hg
    simpa only [d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32111 (p : Pattern) (guard : d4474 p = 1) : d1697 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32110 p hg
    simpa only [d4474, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32112 (p : Pattern) (guard : d4474 p = 1) : d2898 p ≤ (2 : Int) + d7015 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2898, d7015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32106 p hg
    simpa only [d2898, d7015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2898, d7015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32111 p hg
    simpa only [d2898, d7015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32113 (p : Pattern) (guard : d4474 p = 1) : d2899 p ≤ (2 : Int) + d7016 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2899, d7016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d2899, d7016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2899, d7016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32112 p hg
    simpa only [d2899, d7016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32114 (p : Pattern) (guard : d4474 p = 1) : d2900 p ≤ (2 : Int) + d7017 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2900, d7017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d2900, d7017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2900, d7017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32113 p hg
    simpa only [d2900, d7017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32115 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (2 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15694 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1822 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32116 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (2 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32115 p hg
    simpa only [d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32117 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (2 : Int) + d1802 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12098 p hg
    simpa only [d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32116 p hg
    simpa only [d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32118 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (2 : Int) + d1803 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32116 p hg
    simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32119 (p : Pattern) (guard : d0 p = 1) : d1803 p ≤ (2 : Int) + d1803 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32120 (p : Pattern) (guard : d4474 p = 1) : d2901 p ≤ (2 : Int) + d1803 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32118 p hg
    simpa only [d4474, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32119 p hg
    simpa only [d4474, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32121 (p : Pattern) (guard : d1 p = 1) : d1701 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1822 p hg
    simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32122 (p : Pattern) (guard : d1 p = 1) : d1702 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32121 p hg
    simpa only [d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1756 p hg
    simpa only [d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32123 (p : Pattern) (guard : d1 p = 1) : d1703 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1824 p hg
    simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32122 p hg
    simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32124 (p : Pattern) (guard : d1 p = 1) : d1704 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32123 p hg
    simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32122 p hg
    simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32125 (p : Pattern) (guard : d4474 p = 1) : d1705 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32124 p hg
    simpa only [d4474, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32126 (p : Pattern) (guard : d4474 p = 1) : d2902 p ≤ (2 : Int) + d7018 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2902, d7018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32120 p hg
    simpa only [d2902, d7018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2902, d7018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32125 p hg
    simpa only [d2902, d7018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32127 (p : Pattern) (guard : d4474 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare32128 (p : Pattern) (guard : d4474 p = 1) : d2903 p ≤ (2 : Int) + d7019 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2903, d7019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32126 p hg
    simpa only [d2903, d7019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2903, d7019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2903, d7019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32129 (p : Pattern) (guard : d4474 p = 1) : d2904 p ≤ (2 : Int) + d7020 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2904, d7020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32113 p hg
    simpa only [d2904, d7020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2904, d7020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32128 p hg
    simpa only [d2904, d7020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32130 (p : Pattern) (guard : d4474 p = 1) : d2905 p ≤ (2 : Int) + d7021 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2905, d7021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32114 p hg
    simpa only [d2905, d7021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2905, d7021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32129 p hg
    simpa only [d2905, d7021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32131 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d1775 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15669 p hg
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15755 p hg
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32132 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d1776 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32131 p hg
    simpa only [d14, d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15756 p hg
    simpa only [d14, d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32133 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d1777 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32132 p hg
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32134 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d1785 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15669 p hg
    simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15776 p hg
    simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32135 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d1786 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32134 p hg
    simpa only [d14, d1786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4704 p hg
    simpa only [d14, d1786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32136 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d1787 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32090 p hg
    simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32135 p hg
    simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32137 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d1788 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32133 p hg
    simpa only [d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32136 p hg
    simpa only [d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32138 (p : Pattern) (guard : d0 p = 1) : d1788 p ≤ (2 : Int) + d1788 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32139 (p : Pattern) (guard : d4474 p = 1) : d2906 p ≤ (2 : Int) + d1788 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32137 p hg
    simpa only [d4474, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32138 p hg
    simpa only [d4474, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32140 (p : Pattern) (guard : d4474 p = 1) : d2907 p ≤ (2 : Int) + d7022 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2907, d7022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d2907, d7022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2907, d7022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15841 p hg
    simpa only [d2907, d7022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32141 (p : Pattern) (guard : d4474 p = 1) : d2908 p ≤ (2 : Int) + d7022 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2908, d7022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d2908, d7022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2908, d7022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16142 p hg
    simpa only [d2908, d7022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32142 (p : Pattern) (guard : d4474 p = 1) : d2909 p ≤ (2 : Int) + d7022 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32140 p hg
    simpa only [d2909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32141 p hg
    simpa only [d2909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32143 (p : Pattern) (guard : d4474 p = 1) : d2910 p ≤ (2 : Int) + d7022 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2910, d7022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d2910, d7022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2910, d7022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15857 p hg
    simpa only [d2910, d7022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32144 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d1791 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15683 p hg
    simpa only [d1791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4849 p hg
    simpa only [d1791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32145 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d1792 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32144 p hg
    simpa only [d18, d1792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4850 p hg
    simpa only [d18, d1792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32146 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d1793 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7129 p hg
    simpa only [d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32145 p hg
    simpa only [d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32147 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15683 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4711 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32148 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d339 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32147 p hg
    simpa only [d18, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4712 p hg
    simpa only [d18, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32149 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d1796 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d1796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32148 p hg
    simpa only [d1796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32150 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d1797 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32146 p hg
    simpa only [d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32149 p hg
    simpa only [d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32151 (p : Pattern) (guard : d0 p = 1) : d1797 p ≤ (2 : Int) + d1797 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32152 (p : Pattern) (guard : d4474 p = 1) : d2911 p ≤ (2 : Int) + d1797 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32150 p hg
    simpa only [d4474, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32151 p hg
    simpa only [d4474, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32153 (p : Pattern) (guard : d4474 p = 1) : d2912 p ≤ (2 : Int) + d7023 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2912, d7023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32152 p hg
    simpa only [d2912, d7023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2912, d7023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2912, d7023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32154 (p : Pattern) (guard : d4474 p = 1) : d2913 p ≤ (2 : Int) + d7024 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2913, d7024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32143 p hg
    simpa only [d2913, d7024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2913, d7024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32153 p hg
    simpa only [d2913, d7024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32155 (p : Pattern) (guard : d4474 p = 1) : d2914 p ≤ (2 : Int) + d7025 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2914, d7025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32142 p hg
    simpa only [d2914, d7025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2914, d7025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32154 p hg
    simpa only [d2914, d7025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32156 (p : Pattern) (guard : d4474 p = 1) : d2915 p ≤ (2 : Int) + d7022 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2915, d7022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d2915, d7022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2915, d7022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2915, d7022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32157 (p : Pattern) (guard : d4474 p = 1) : d2916 p ≤ (2 : Int) + d7024 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2916, d7024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32156 p hg
    simpa only [d2916, d7024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2916, d7024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32153 p hg
    simpa only [d2916, d7024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32158 (p : Pattern) (guard : d4474 p = 1) : d2917 p ≤ (2 : Int) + d7018 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2917, d7018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32120 p hg
    simpa only [d2917, d7018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2917, d7018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2917, d7018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32159 (p : Pattern) (guard : d4474 p = 1) : d2918 p ≤ (2 : Int) + d7019 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2918, d7019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32158 p hg
    simpa only [d2918, d7019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2918, d7019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2918, d7019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32160 (p : Pattern) (guard : d4474 p = 1) : d2919 p ≤ (2 : Int) + d7026 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2919, d7026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32157 p hg
    simpa only [d2919, d7026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2919, d7026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32159 p hg
    simpa only [d2919, d7026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32161 (p : Pattern) (guard : d4474 p = 1) : d2920 p ≤ (2 : Int) + d7027 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2920, d7027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32155 p hg
    simpa only [d2920, d7027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2920, d7027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32160 p hg
    simpa only [d2920, d7027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32162 (p : Pattern) (guard : d4474 p = 1) : d2921 p ≤ (2 : Int) + d7028 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2921, d7028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32130 p hg
    simpa only [d2921, d7028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2921, d7028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32161 p hg
    simpa only [d2921, d7028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32163 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d1713 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15711 p hg
    simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24648 p hg
    simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32164 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d1714 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32163 p hg
    simpa only [d31, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24649 p hg
    simpa only [d31, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32165 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d2029 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32164 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32166 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d2030 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32165 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32164 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32167 (p : Pattern) (guard : d0 p = 1) : d2030 p ≤ (2 : Int) + d2030 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32168 (p : Pattern) (guard : d4474 p = 1) : d2922 p ≤ (2 : Int) + d2030 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32166 p hg
    simpa only [d4474, d2922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32167 p hg
    simpa only [d4474, d2922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32169 (p : Pattern) (guard : d1 p = 1) : d1742 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12151 p hg
    simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4711 p hg
    simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32170 (p : Pattern) (guard : d1 p = 1) : d1743 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32169 p hg
    simpa only [d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4712 p hg
    simpa only [d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32171 (p : Pattern) (guard : d1 p = 1) : d1744 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12153 p hg
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32170 p hg
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32172 (p : Pattern) (guard : d1 p = 1) : d1745 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32171 p hg
    simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32170 p hg
    simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32173 (p : Pattern) (guard : d4474 p = 1) : d1746 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32172 p hg
    simpa only [d4474, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32174 (p : Pattern) (guard : d4474 p = 1) : d2923 p ≤ (2 : Int) + d7029 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2923, d7029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32168 p hg
    simpa only [d2923, d7029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2923, d7029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32173 p hg
    simpa only [d2923, d7029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32175 (p : Pattern) (guard : d4474 p = 1) : d2924 p ≤ (2 : Int) + d7030 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2924, d7030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d2924, d7030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2924, d7030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32174 p hg
    simpa only [d2924, d7030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32176 (p : Pattern) (guard : d4474 p = 1) : d2925 p ≤ (2 : Int) + d7031 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2925, d7031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32112 p hg
    simpa only [d2925, d7031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2925, d7031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32126 p hg
    simpa only [d2925, d7031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32177 (p : Pattern) (guard : d4474 p = 1) : d2926 p ≤ (2 : Int) + d7032 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2926, d7032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32175 p hg
    simpa only [d2926, d7032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2926, d7032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32176 p hg
    simpa only [d2926, d7032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32178 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (2 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15723 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1829 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32179 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (2 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32178 p hg
    simpa only [d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32180 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (2 : Int) + d1751 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2175 p hg
    simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32179 p hg
    simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32181 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (2 : Int) + d1752 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32180 p hg
    simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32179 p hg
    simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32182 (p : Pattern) (guard : d0 p = 1) : d1752 p ≤ (2 : Int) + d1752 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32183 (p : Pattern) (guard : d4474 p = 1) : d2927 p ≤ (2 : Int) + d1752 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32181 p hg
    simpa only [d4474, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32182 p hg
    simpa only [d4474, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32184 (p : Pattern) (guard : d4474 p = 1) : d2928 p ≤ (2 : Int) + d7033 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2928, d7033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32183 p hg
    simpa only [d2928, d7033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2928, d7033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15850 p hg
    simpa only [d2928, d7033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32185 (p : Pattern) (guard : d4474 p = 1) : d2929 p ≤ (2 : Int) + d7034 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2929, d7034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32112 p hg
    simpa only [d2929, d7034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2929, d7034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32184 p hg
    simpa only [d2929, d7034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32186 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15733 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32187 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (2 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32186 p hg
    simpa only [d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1756 p hg
    simpa only [d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32188 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (2 : Int) + d1728 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12115 p hg
    simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32187 p hg
    simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32189 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (2 : Int) + d1729 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32188 p hg
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32187 p hg
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32190 (p : Pattern) (guard : d0 p = 1) : d1729 p ≤ (2 : Int) + d1729 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32191 (p : Pattern) (guard : d4474 p = 1) : d2930 p ≤ (2 : Int) + d1729 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32189 p hg
    simpa only [d4474, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32190 p hg
    simpa only [d4474, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32192 (p : Pattern) (guard : d4474 p = 1) : d2931 p ≤ (2 : Int) + d7035 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2931, d7035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32191 p hg
    simpa only [d2931, d7035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2931, d7035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15857 p hg
    simpa only [d2931, d7035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32193 (p : Pattern) (guard : d4474 p = 1) : d2932 p ≤ (2 : Int) + d7036 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2932, d7036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32192 p hg
    simpa only [d2932, d7036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2932, d7036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d2932, d7036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32194 (p : Pattern) (guard : d4474 p = 1) : d2933 p ≤ (2 : Int) + d7037 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2933, d7037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32185 p hg
    simpa only [d2933, d7037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2933, d7037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32193 p hg
    simpa only [d2933, d7037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32195 (p : Pattern) (guard : d4474 p = 1) : d2934 p ≤ (2 : Int) + d7038 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2934, d7038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32177 p hg
    simpa only [d2934, d7038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2934, d7038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32194 p hg
    simpa only [d2934, d7038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32196 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d1710 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15711 p hg
    simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16151 p hg
    simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32197 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d1711 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32196 p hg
    simpa only [d31, d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16152 p hg
    simpa only [d31, d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32198 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d1712 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32197 p hg
    simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32199 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d30 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15711 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12151 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
