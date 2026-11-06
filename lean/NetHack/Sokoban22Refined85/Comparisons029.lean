/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4060 (p : Pattern) (guard : d4304 p = 1) : d708 p ≤ (4 : Int) + d4392 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d708, d4392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4020 p hg
    simpa only [d708, d4392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d708, d4392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d708, d4392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4061 (p : Pattern) (guard : d4304 p = 1) : d709 p ≤ (4 : Int) + d4393 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d709, d4393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4011 p hg
    simpa only [d709, d4393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d709, d4393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4060 p hg
    simpa only [d709, d4393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4062 (p : Pattern) (guard : d4148 p = 1) : d22 p ≤ (0 : Int) + d22 p := by
  omega
theorem compare4063 (p : Pattern) (guard : d0 p = 1) : d20 p ≤ (0 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4064 (p : Pattern) (guard : d4148 p = 1) : d21 p ≤ (0 : Int) + d950 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d21, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d21, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d21, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4063 p hg
    simpa only [d4148, d21, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4065 (p : Pattern) (guard : d4148 p = 1) : d28 p ≤ (0 : Int) + d1399 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d28, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4064 p hg
    simpa only [d28, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d28, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d28, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4066 (p : Pattern) (guard : d4148 p = 1) : d29 p ≤ (0 : Int) + d1400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d29, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4062 p hg
    simpa only [d29, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d29, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4065 p hg
    simpa only [d29, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4067 (p : Pattern) (guard : d0 p = 1) : d37 p ≤ (0 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4068 (p : Pattern) (guard : d4148 p = 1) : d38 p ≤ (0 : Int) + d33 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4148, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4067 p hg
    simpa only [d4148, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4069 (p : Pattern) (guard : d4148 p = 1) : d44 p ≤ (0 : Int) + d44 p := by
  omega
theorem compare4070 (p : Pattern) (guard : d4148 p = 1) : d45 p ≤ (0 : Int) + d1401 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d45, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4068 p hg
    simpa only [d45, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d45, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4069 p hg
    simpa only [d45, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4071 (p : Pattern) (guard : d4148 p = 1) : d50 p ≤ (0 : Int) + d50 p := by
  omega
theorem compare4072 (p : Pattern) (guard : d4148 p = 1) : d51 p ≤ (0 : Int) + d1402 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d51, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4070 p hg
    simpa only [d51, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d51, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4071 p hg
    simpa only [d51, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4073 (p : Pattern) (guard : d4148 p = 1) : d52 p ≤ (0 : Int) + d1403 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d52, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4066 p hg
    simpa only [d52, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d52, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4072 p hg
    simpa only [d52, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4074 (p : Pattern) (guard : d0 p = 1) : d392 p ≤ (0 : Int) + d1409 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4075 (p : Pattern) (guard : d4303 p = 1) : d653 p ≤ (0 : Int) + d1410 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d653, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4073 p hg
    simpa only [d4303, d653, d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d653, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4074 p hg
    simpa only [d4303, d653, d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4076 (p : Pattern) (guard : d0 p = 1) : d20 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4077 (p : Pattern) (guard : d4148 p = 1) : d21 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d21, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d21, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d21, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4076 p hg
    simpa only [d4148, d21, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4078 (p : Pattern) (guard : d4148 p = 1) : d28 p ≤ (0 : Int) + d1411 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d28, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4077 p hg
    simpa only [d28, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d28, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d28, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4079 (p : Pattern) (guard : d4148 p = 1) : d29 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d29, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4062 p hg
    simpa only [d29, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d29, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4078 p hg
    simpa only [d29, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4080 (p : Pattern) (guard : d0 p = 1) : d78 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4081 (p : Pattern) (guard : d4148 p = 1) : d79 p ≤ (0 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4080 p hg
    simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4082 (p : Pattern) (guard : d4148 p = 1) : d80 p ≤ (0 : Int) + d1413 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d80, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4081 p hg
    simpa only [d80, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d80, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d80, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4083 (p : Pattern) (guard : d4148 p = 1) : d81 p ≤ (0 : Int) + d1414 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d81, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4082 p hg
    simpa only [d81, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d81, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d81, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4084 (p : Pattern) (guard : d4148 p = 1) : d82 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d82, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4079 p hg
    simpa only [d82, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d82, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4083 p hg
    simpa only [d82, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4085 (p : Pattern) (guard : d0 p = 1) : d399 p ≤ (0 : Int) + d1419 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4086 (p : Pattern) (guard : d4303 p = 1) : d654 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d654, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4084 p hg
    simpa only [d4303, d654, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d654, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4085 p hg
    simpa only [d4303, d654, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4087 (p : Pattern) (guard : d4303 p = 1) : d655 p ≤ (0 : Int) + d1421 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d655, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4075 p hg
    simpa only [d655, d1421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d655, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4086 p hg
    simpa only [d655, d1421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4088 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (0 : Int) + d1419 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4089 (p : Pattern) (guard : d4303 p = 1) : d656 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d656, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4084 p hg
    simpa only [d4303, d656, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d656, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4088 p hg
    simpa only [d4303, d656, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4090 (p : Pattern) (guard : d4148 p = 1) : d94 p ≤ (0 : Int) + d94 p := by
  omega
theorem compare4091 (p : Pattern) (guard : d4303 p = 1) : d657 p ≤ (0 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d657, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4090 p hg
    simpa only [d4303, d657, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d657, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3451 p hg
    simpa only [d4303, d657, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4092 (p : Pattern) (guard : d4303 p = 1) : d658 p ≤ (0 : Int) + d1422 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d658, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4089 p hg
    simpa only [d658, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d658, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4091 p hg
    simpa only [d658, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4093 (p : Pattern) (guard : d4303 p = 1) : d659 p ≤ (0 : Int) + d1423 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d659, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4087 p hg
    simpa only [d659, d1423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d659, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4092 p hg
    simpa only [d659, d1423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4094 (p : Pattern) (guard : d0 p = 1) : d397 p ≤ (0 : Int) + d1425 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4095 (p : Pattern) (guard : d4303 p = 1) : d660 p ≤ (0 : Int) + d1426 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d660, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4073 p hg
    simpa only [d4303, d660, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d660, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4094 p hg
    simpa only [d4303, d660, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4096 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (0 : Int) + d1419 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4097 (p : Pattern) (guard : d4303 p = 1) : d661 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d661, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4084 p hg
    simpa only [d4303, d661, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d661, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4096 p hg
    simpa only [d4303, d661, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4098 (p : Pattern) (guard : d4303 p = 1) : d662 p ≤ (0 : Int) + d1427 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d662, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4095 p hg
    simpa only [d662, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d662, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4097 p hg
    simpa only [d662, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4099 (p : Pattern) (guard : d0 p = 1) : d410 p ≤ (0 : Int) + d1419 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4100 (p : Pattern) (guard : d4303 p = 1) : d663 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d663, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4084 p hg
    simpa only [d4303, d663, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d663, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4099 p hg
    simpa only [d4303, d663, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4101 (p : Pattern) (guard : d4303 p = 1) : d664 p ≤ (0 : Int) + d1428 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d664, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4100 p hg
    simpa only [d664, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d664, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d664, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4102 (p : Pattern) (guard : d4303 p = 1) : d665 p ≤ (0 : Int) + d1429 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d665, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4098 p hg
    simpa only [d665, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d665, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4101 p hg
    simpa only [d665, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4103 (p : Pattern) (guard : d4303 p = 1) : d666 p ≤ (0 : Int) + d1430 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d666, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4093 p hg
    simpa only [d666, d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d666, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4102 p hg
    simpa only [d666, d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4104 (p : Pattern) (guard : d0 p = 1) : d418 p ≤ (0 : Int) + d1433 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4105 (p : Pattern) (guard : d4303 p = 1) : d667 p ≤ (0 : Int) + d1434 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d667, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4073 p hg
    simpa only [d4303, d667, d1434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d667, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4104 p hg
    simpa only [d4303, d667, d1434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4106 (p : Pattern) (guard : d0 p = 1) : d420 p ≤ (0 : Int) + d1419 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4107 (p : Pattern) (guard : d4303 p = 1) : d668 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d668, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4084 p hg
    simpa only [d4303, d668, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d668, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4106 p hg
    simpa only [d4303, d668, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4108 (p : Pattern) (guard : d4303 p = 1) : d669 p ≤ (0 : Int) + d1435 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d669, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4105 p hg
    simpa only [d669, d1435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d669, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4107 p hg
    simpa only [d669, d1435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4109 (p : Pattern) (guard : d4303 p = 1) : d670 p ≤ (0 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d670, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4090 p hg
    simpa only [d4303, d670, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d670, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3470 p hg
    simpa only [d4303, d670, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4110 (p : Pattern) (guard : d4303 p = 1) : d671 p ≤ (0 : Int) + d1422 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d671, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4086 p hg
    simpa only [d671, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d671, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4109 p hg
    simpa only [d671, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4111 (p : Pattern) (guard : d4303 p = 1) : d672 p ≤ (0 : Int) + d1436 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d672, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4108 p hg
    simpa only [d672, d1436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d672, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4110 p hg
    simpa only [d672, d1436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4112 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (0 : Int) + d1425 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4113 (p : Pattern) (guard : d4303 p = 1) : d673 p ≤ (0 : Int) + d1426 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d673, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4073 p hg
    simpa only [d4303, d673, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d673, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4112 p hg
    simpa only [d4303, d673, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4114 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (0 : Int) + d1419 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4115 (p : Pattern) (guard : d4303 p = 1) : d674 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d674, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4084 p hg
    simpa only [d4303, d674, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d674, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4114 p hg
    simpa only [d4303, d674, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4116 (p : Pattern) (guard : d4303 p = 1) : d675 p ≤ (0 : Int) + d1427 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d675, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4113 p hg
    simpa only [d675, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d675, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4115 p hg
    simpa only [d675, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4117 (p : Pattern) (guard : d4303 p = 1) : d676 p ≤ (0 : Int) + d1428 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d676, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4097 p hg
    simpa only [d676, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d676, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d676, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4118 (p : Pattern) (guard : d4303 p = 1) : d677 p ≤ (0 : Int) + d1429 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d677, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4116 p hg
    simpa only [d677, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d677, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4117 p hg
    simpa only [d677, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4119 (p : Pattern) (guard : d4303 p = 1) : d678 p ≤ (0 : Int) + d1437 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d678, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4111 p hg
    simpa only [d678, d1437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d678, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4118 p hg
    simpa only [d678, d1437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4120 (p : Pattern) (guard : d4303 p = 1) : d679 p ≤ (0 : Int) + d1438 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d679, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4103 p hg
    simpa only [d679, d1438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d679, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4119 p hg
    simpa only [d679, d1438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4121 (p : Pattern) (guard : d4148 p = 1) : d111 p ≤ (0 : Int) + d111 p := by
  omega
theorem compare4122 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (0 : Int) + d118 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4123 (p : Pattern) (guard : d4148 p = 1) : d110 p ≤ (0 : Int) + d1043 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d110, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d110, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d110, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4122 p hg
    simpa only [d4148, d110, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4124 (p : Pattern) (guard : d4148 p = 1) : d113 p ≤ (0 : Int) + d1439 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d113, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4123 p hg
    simpa only [d113, d1439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d113, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d113, d1439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4125 (p : Pattern) (guard : d4148 p = 1) : d114 p ≤ (0 : Int) + d1440 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d114, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4121 p hg
    simpa only [d114, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d114, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4124 p hg
    simpa only [d114, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4126 (p : Pattern) (guard : d0 p = 1) : d122 p ≤ (0 : Int) + d118 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4127 (p : Pattern) (guard : d4148 p = 1) : d123 p ≤ (0 : Int) + d118 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4148, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4126 p hg
    simpa only [d4148, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4128 (p : Pattern) (guard : d4148 p = 1) : d126 p ≤ (0 : Int) + d126 p := by
  omega
theorem compare4129 (p : Pattern) (guard : d4148 p = 1) : d127 p ≤ (0 : Int) + d1441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d127, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4127 p hg
    simpa only [d127, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d127, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4128 p hg
    simpa only [d127, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4130 (p : Pattern) (guard : d4148 p = 1) : d129 p ≤ (0 : Int) + d129 p := by
  omega
theorem compare4131 (p : Pattern) (guard : d4148 p = 1) : d130 p ≤ (0 : Int) + d1442 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d130, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4129 p hg
    simpa only [d130, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d130, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4130 p hg
    simpa only [d130, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4132 (p : Pattern) (guard : d4148 p = 1) : d131 p ≤ (0 : Int) + d1443 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d131, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4125 p hg
    simpa only [d131, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d131, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4131 p hg
    simpa only [d131, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4133 (p : Pattern) (guard : d0 p = 1) : d418 p ≤ (0 : Int) + d1448 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4134 (p : Pattern) (guard : d4303 p = 1) : d680 p ≤ (0 : Int) + d1449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d680, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4132 p hg
    simpa only [d4303, d680, d1449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d680, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4133 p hg
    simpa only [d4303, d680, d1449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4135 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (0 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4136 (p : Pattern) (guard : d4148 p = 1) : d110 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d110, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d110, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d110, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4135 p hg
    simpa only [d4148, d110, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4137 (p : Pattern) (guard : d4148 p = 1) : d113 p ≤ (0 : Int) + d1450 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d113, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4136 p hg
    simpa only [d113, d1450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d113, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d113, d1450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4138 (p : Pattern) (guard : d4148 p = 1) : d114 p ≤ (0 : Int) + d1451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d114, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4121 p hg
    simpa only [d114, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d114, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4137 p hg
    simpa only [d114, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4139 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4140 (p : Pattern) (guard : d4148 p = 1) : d149 p ≤ (0 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4139 p hg
    simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4141 (p : Pattern) (guard : d4148 p = 1) : d150 p ≤ (0 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d150, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4140 p hg
    simpa only [d150, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d150, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d150, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4142 (p : Pattern) (guard : d4148 p = 1) : d151 p ≤ (0 : Int) + d1062 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d151, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4141 p hg
    simpa only [d151, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d151, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d151, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4143 (p : Pattern) (guard : d4148 p = 1) : d152 p ≤ (0 : Int) + d1452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d152, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4138 p hg
    simpa only [d152, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d152, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4142 p hg
    simpa only [d152, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4144 (p : Pattern) (guard : d0 p = 1) : d420 p ≤ (0 : Int) + d1455 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4145 (p : Pattern) (guard : d4303 p = 1) : d681 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d681, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4143 p hg
    simpa only [d4303, d681, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d681, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4144 p hg
    simpa only [d4303, d681, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4146 (p : Pattern) (guard : d4303 p = 1) : d682 p ≤ (0 : Int) + d1457 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d682, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4134 p hg
    simpa only [d682, d1457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d682, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4145 p hg
    simpa only [d682, d1457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4147 (p : Pattern) (guard : d0 p = 1) : d399 p ≤ (0 : Int) + d1455 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4148 (p : Pattern) (guard : d4303 p = 1) : d683 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d683, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4143 p hg
    simpa only [d4303, d683, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d683, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4147 p hg
    simpa only [d4303, d683, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4149 (p : Pattern) (guard : d4303 p = 1) : d684 p ≤ (0 : Int) + d1458 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d684, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4148 p hg
    simpa only [d684, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d684, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3792 p hg
    simpa only [d684, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4150 (p : Pattern) (guard : d4303 p = 1) : d685 p ≤ (0 : Int) + d1459 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d685, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4146 p hg
    simpa only [d685, d1459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d685, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4149 p hg
    simpa only [d685, d1459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4151 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (0 : Int) + d1461 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4152 (p : Pattern) (guard : d4303 p = 1) : d686 p ≤ (0 : Int) + d1462 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d686, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4132 p hg
    simpa only [d4303, d686, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d686, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4151 p hg
    simpa only [d4303, d686, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4153 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (0 : Int) + d1455 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4154 (p : Pattern) (guard : d4303 p = 1) : d687 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d687, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4143 p hg
    simpa only [d4303, d687, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d687, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4153 p hg
    simpa only [d4303, d687, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4155 (p : Pattern) (guard : d4303 p = 1) : d688 p ≤ (0 : Int) + d1463 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d688, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4152 p hg
    simpa only [d688, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d688, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4154 p hg
    simpa only [d688, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4156 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (0 : Int) + d1455 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4157 (p : Pattern) (guard : d4303 p = 1) : d689 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d689, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4143 p hg
    simpa only [d4303, d689, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d689, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4156 p hg
    simpa only [d4303, d689, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4158 (p : Pattern) (guard : d4303 p = 1) : d690 p ≤ (0 : Int) + d1464 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d690, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4157 p hg
    simpa only [d690, d1464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d690, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d690, d1464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4159 (p : Pattern) (guard : d4303 p = 1) : d691 p ≤ (0 : Int) + d1465 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d691, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4155 p hg
    simpa only [d691, d1465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d691, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4158 p hg
    simpa only [d691, d1465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4160 (p : Pattern) (guard : d4303 p = 1) : d692 p ≤ (0 : Int) + d1466 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d692, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4150 p hg
    simpa only [d692, d1466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d692, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4159 p hg
    simpa only [d692, d1466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4161 (p : Pattern) (guard : d4303 p = 1) : d693 p ≤ (0 : Int) + d1467 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d693, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4103 p hg
    simpa only [d693, d1467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d693, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4160 p hg
    simpa only [d693, d1467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4162 (p : Pattern) (guard : d4303 p = 1) : d694 p ≤ (0 : Int) + d1468 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d694, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4120 p hg
    simpa only [d694, d1468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d694, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4161 p hg
    simpa only [d694, d1468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4163 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (0 : Int) + d1471 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4164 (p : Pattern) (guard : d4303 p = 1) : d674 p ≤ (0 : Int) + d1472 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d674, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4084 p hg
    simpa only [d4303, d674, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d674, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4163 p hg
    simpa only [d4303, d674, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4165 (p : Pattern) (guard : d4303 p = 1) : d675 p ≤ (0 : Int) + d1473 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d675, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4113 p hg
    simpa only [d675, d1473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d675, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4164 p hg
    simpa only [d675, d1473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4166 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (0 : Int) + d1471 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4167 (p : Pattern) (guard : d4303 p = 1) : d661 p ≤ (0 : Int) + d1472 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d661, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4084 p hg
    simpa only [d4303, d661, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d661, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4166 p hg
    simpa only [d4303, d661, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4168 (p : Pattern) (guard : d4303 p = 1) : d676 p ≤ (0 : Int) + d1474 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d676, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4167 p hg
    simpa only [d676, d1474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d676, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d676, d1474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4169 (p : Pattern) (guard : d4303 p = 1) : d677 p ≤ (0 : Int) + d1475 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d677, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4165 p hg
    simpa only [d677, d1475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d677, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4168 p hg
    simpa only [d677, d1475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4170 (p : Pattern) (guard : d4303 p = 1) : d678 p ≤ (0 : Int) + d1476 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d678, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4111 p hg
    simpa only [d678, d1476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d678, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4169 p hg
    simpa only [d678, d1476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4171 (p : Pattern) (guard : d4303 p = 1) : d679 p ≤ (0 : Int) + d1477 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d679, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4103 p hg
    simpa only [d679, d1477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d679, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4170 p hg
    simpa only [d679, d1477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4172 (p : Pattern) (guard : d0 p = 1) : d453 p ≤ (0 : Int) + d1461 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4173 (p : Pattern) (guard : d4303 p = 1) : d695 p ≤ (0 : Int) + d1462 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d695, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4132 p hg
    simpa only [d4303, d695, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d695, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4172 p hg
    simpa only [d4303, d695, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4174 (p : Pattern) (guard : d0 p = 1) : d456 p ≤ (0 : Int) + d1455 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4175 (p : Pattern) (guard : d4303 p = 1) : d696 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d696, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4143 p hg
    simpa only [d4303, d696, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d696, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4174 p hg
    simpa only [d4303, d696, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4176 (p : Pattern) (guard : d4303 p = 1) : d697 p ≤ (0 : Int) + d1463 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d697, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4173 p hg
    simpa only [d697, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d697, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4175 p hg
    simpa only [d697, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4177 (p : Pattern) (guard : d0 p = 1) : d461 p ≤ (0 : Int) + d1455 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4178 (p : Pattern) (guard : d4303 p = 1) : d698 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d698, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4143 p hg
    simpa only [d4303, d698, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d698, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4177 p hg
    simpa only [d4303, d698, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4179 (p : Pattern) (guard : d4303 p = 1) : d699 p ≤ (0 : Int) + d1458 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d699, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4178 p hg
    simpa only [d699, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d699, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3792 p hg
    simpa only [d699, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4180 (p : Pattern) (guard : d4303 p = 1) : d700 p ≤ (0 : Int) + d1478 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d700, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4176 p hg
    simpa only [d700, d1478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d700, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4179 p hg
    simpa only [d700, d1478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4181 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (0 : Int) + d269 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4182 (p : Pattern) (guard : d4148 p = 1) : d110 p ≤ (0 : Int) + d291 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d110, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d110, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d110, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4181 p hg
    simpa only [d4148, d110, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4183 (p : Pattern) (guard : d4148 p = 1) : d113 p ≤ (0 : Int) + d1479 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d113, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4182 p hg
    simpa only [d113, d1479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d113, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d113, d1479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4184 (p : Pattern) (guard : d4148 p = 1) : d114 p ≤ (0 : Int) + d1480 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d114, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4121 p hg
    simpa only [d114, d1480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d114, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4183 p hg
    simpa only [d114, d1480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4185 (p : Pattern) (guard : d0 p = 1) : d270 p ≤ (0 : Int) + d269 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4186 (p : Pattern) (guard : d4148 p = 1) : d271 p ≤ (0 : Int) + d269 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4148, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4185 p hg
    simpa only [d4148, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4187 (p : Pattern) (guard : d4148 p = 1) : d275 p ≤ (0 : Int) + d275 p := by
  omega
theorem compare4188 (p : Pattern) (guard : d4148 p = 1) : d276 p ≤ (0 : Int) + d1481 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d276, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4186 p hg
    simpa only [d276, d1481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d276, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4187 p hg
    simpa only [d276, d1481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4189 (p : Pattern) (guard : d4148 p = 1) : d279 p ≤ (0 : Int) + d279 p := by
  omega
theorem compare4190 (p : Pattern) (guard : d4148 p = 1) : d280 p ≤ (0 : Int) + d1482 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d280, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4188 p hg
    simpa only [d280, d1482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d280, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4189 p hg
    simpa only [d280, d1482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4191 (p : Pattern) (guard : d4148 p = 1) : d281 p ≤ (0 : Int) + d1483 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d281, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4184 p hg
    simpa only [d281, d1483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d281, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4190 p hg
    simpa only [d281, d1483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4192 (p : Pattern) (guard : d0 p = 1) : d471 p ≤ (0 : Int) + d1487 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4193 (p : Pattern) (guard : d4303 p = 1) : d701 p ≤ (0 : Int) + d1488 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d701, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4191 p hg
    simpa only [d4303, d701, d1488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d701, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4192 p hg
    simpa only [d4303, d701, d1488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4194 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (0 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4195 (p : Pattern) (guard : d4148 p = 1) : d291 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4194 p hg
    simpa only [d4148, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4196 (p : Pattern) (guard : d4148 p = 1) : d293 p ≤ (0 : Int) + d293 p := by
  omega
theorem compare4197 (p : Pattern) (guard : d4148 p = 1) : d294 p ≤ (0 : Int) + d1489 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d294, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4195 p hg
    simpa only [d294, d1489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d294, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4196 p hg
    simpa only [d294, d1489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4198 (p : Pattern) (guard : d0 p = 1) : d292 p ≤ (0 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4199 (p : Pattern) (guard : d4148 p = 1) : d293 p ≤ (0 : Int) + d1133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d293, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4148, d293, d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d293, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4198 p hg
    simpa only [d4148, d293, d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
