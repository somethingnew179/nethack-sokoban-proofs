/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4340 (p : Pattern) (guard : d4397 p = 1) : d111 p ≤ (0 : Int) + d1070 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d111, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d4397, d111, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d111, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4339 p hg
    simpa only [d4397, d111, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4341 (p : Pattern) (guard : d4397 p = 1) : d114 p ≤ (0 : Int) + d1071 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d114, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4340 p hg
    simpa only [d114, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d114, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4331 p hg
    simpa only [d114, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4342 (p : Pattern) (guard : d4397 p = 1) : d152 p ≤ (0 : Int) + d1072 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d152, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4341 p hg
    simpa only [d152, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d152, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4334 p hg
    simpa only [d152, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4343 (p : Pattern) (guard : d0 p = 1) : d399 p ≤ (0 : Int) + d1075 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4344 (p : Pattern) (guard : d4398 p = 1) : d683 p ≤ (0 : Int) + d1076 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d683, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4342 p hg
    simpa only [d4398, d683, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d683, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4343 p hg
    simpa only [d4398, d683, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4345 (p : Pattern) (guard : d4398 p = 1) : d162 p ≤ (0 : Int) + d162 p := by
  omega
theorem compare4346 (p : Pattern) (guard : d4398 p = 1) : d684 p ≤ (0 : Int) + d1077 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d684, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4344 p hg
    simpa only [d684, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d684, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4345 p hg
    simpa only [d684, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4347 (p : Pattern) (guard : d4398 p = 1) : d685 p ≤ (0 : Int) + d1078 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d685, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4338 p hg
    simpa only [d685, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d685, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4346 p hg
    simpa only [d685, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4348 (p : Pattern) (guard : d0 p = 1) : d110 p ≤ (0 : Int) + d389 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4349 (p : Pattern) (guard : d4397 p = 1) : d111 p ≤ (0 : Int) + d1079 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d111, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d4397, d111, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d111, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4348 p hg
    simpa only [d4397, d111, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4350 (p : Pattern) (guard : d4397 p = 1) : d113 p ≤ (0 : Int) + d1080 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d113, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4123 p hg
    simpa only [d4397, d113, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d113, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d4397, d113, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4351 (p : Pattern) (guard : d4397 p = 1) : d114 p ≤ (0 : Int) + d1081 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d114, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4349 p hg
    simpa only [d114, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d114, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4350 p hg
    simpa only [d114, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4352 (p : Pattern) (guard : d0 p = 1) : d126 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4353 (p : Pattern) (guard : d4397 p = 1) : d127 p ≤ (0 : Int) + d1082 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d127, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4127 p hg
    simpa only [d4397, d127, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d127, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4352 p hg
    simpa only [d4397, d127, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4354 (p : Pattern) (guard : d4397 p = 1) : d130 p ≤ (0 : Int) + d1083 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d130, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4353 p hg
    simpa only [d130, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d130, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4323 p hg
    simpa only [d130, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4355 (p : Pattern) (guard : d4397 p = 1) : d131 p ≤ (0 : Int) + d1084 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d131, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4351 p hg
    simpa only [d131, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d131, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4354 p hg
    simpa only [d131, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4356 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (0 : Int) + d1087 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4357 (p : Pattern) (guard : d4398 p = 1) : d686 p ≤ (0 : Int) + d1088 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d686, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4355 p hg
    simpa only [d4398, d686, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d686, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4356 p hg
    simpa only [d4398, d686, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4358 (p : Pattern) (guard : d0 p = 1) : d110 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4359 (p : Pattern) (guard : d4397 p = 1) : d111 p ≤ (0 : Int) + d1089 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d111, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d4397, d111, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d111, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4358 p hg
    simpa only [d4397, d111, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4360 (p : Pattern) (guard : d4397 p = 1) : d114 p ≤ (0 : Int) + d1090 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d114, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4359 p hg
    simpa only [d114, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d114, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4331 p hg
    simpa only [d114, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4361 (p : Pattern) (guard : d4397 p = 1) : d152 p ≤ (0 : Int) + d1091 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d152, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4360 p hg
    simpa only [d152, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d152, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4334 p hg
    simpa only [d152, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4362 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (0 : Int) + d1067 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4363 (p : Pattern) (guard : d4398 p = 1) : d687 p ≤ (0 : Int) + d1092 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d687, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4361 p hg
    simpa only [d4398, d687, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d687, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4362 p hg
    simpa only [d4398, d687, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4364 (p : Pattern) (guard : d4398 p = 1) : d688 p ≤ (0 : Int) + d1093 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d688, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4357 p hg
    simpa only [d688, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d688, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4363 p hg
    simpa only [d688, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4365 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (0 : Int) + d1067 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4366 (p : Pattern) (guard : d4398 p = 1) : d689 p ≤ (0 : Int) + d1092 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d689, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4361 p hg
    simpa only [d4398, d689, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d689, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4365 p hg
    simpa only [d4398, d689, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4367 (p : Pattern) (guard : d4398 p = 1) : d690 p ≤ (0 : Int) + d1094 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d690, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4366 p hg
    simpa only [d690, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d690, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4278 p hg
    simpa only [d690, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4368 (p : Pattern) (guard : d4398 p = 1) : d691 p ≤ (0 : Int) + d1095 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d691, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4364 p hg
    simpa only [d691, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d691, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4367 p hg
    simpa only [d691, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4369 (p : Pattern) (guard : d4398 p = 1) : d692 p ≤ (0 : Int) + d1096 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d692, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4347 p hg
    simpa only [d692, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d692, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4368 p hg
    simpa only [d692, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4370 (p : Pattern) (guard : d4398 p = 1) : d693 p ≤ (0 : Int) + d1097 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d693, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4281 p hg
    simpa only [d693, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d693, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4369 p hg
    simpa only [d693, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4371 (p : Pattern) (guard : d4398 p = 1) : d694 p ≤ (0 : Int) + d1098 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d694, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4313 p hg
    simpa only [d694, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d694, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4370 p hg
    simpa only [d694, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4372 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (0 : Int) + d1102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4373 (p : Pattern) (guard : d4398 p = 1) : d674 p ≤ (0 : Int) + d1103 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d674, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4268 p hg
    simpa only [d4398, d674, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d674, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4372 p hg
    simpa only [d4398, d674, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4374 (p : Pattern) (guard : d4398 p = 1) : d675 p ≤ (0 : Int) + d1104 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d675, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4306 p hg
    simpa only [d675, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d675, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4373 p hg
    simpa only [d675, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4375 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (0 : Int) + d1102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4376 (p : Pattern) (guard : d4398 p = 1) : d661 p ≤ (0 : Int) + d1103 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d661, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4268 p hg
    simpa only [d4398, d661, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d661, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4375 p hg
    simpa only [d4398, d661, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4377 (p : Pattern) (guard : d4398 p = 1) : d676 p ≤ (0 : Int) + d1105 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d676, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4376 p hg
    simpa only [d676, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d676, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4278 p hg
    simpa only [d676, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4378 (p : Pattern) (guard : d4398 p = 1) : d677 p ≤ (0 : Int) + d1106 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d677, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4374 p hg
    simpa only [d677, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d677, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4377 p hg
    simpa only [d677, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4379 (p : Pattern) (guard : d4398 p = 1) : d678 p ≤ (0 : Int) + d1107 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d678, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4302 p hg
    simpa only [d678, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d678, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4378 p hg
    simpa only [d678, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4380 (p : Pattern) (guard : d4398 p = 1) : d679 p ≤ (0 : Int) + d1108 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d679, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4281 p hg
    simpa only [d679, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d679, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4379 p hg
    simpa only [d679, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4381 (p : Pattern) (guard : d0 p = 1) : d453 p ≤ (0 : Int) + d1111 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4382 (p : Pattern) (guard : d4398 p = 1) : d695 p ≤ (0 : Int) + d1112 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d695, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4325 p hg
    simpa only [d4398, d695, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d695, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4381 p hg
    simpa only [d4398, d695, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4383 (p : Pattern) (guard : d0 p = 1) : d456 p ≤ (0 : Int) + d1067 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4384 (p : Pattern) (guard : d4398 p = 1) : d696 p ≤ (0 : Int) + d1068 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d696, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4335 p hg
    simpa only [d4398, d696, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d696, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4383 p hg
    simpa only [d4398, d696, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4385 (p : Pattern) (guard : d4398 p = 1) : d697 p ≤ (0 : Int) + d1113 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d697, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4382 p hg
    simpa only [d697, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d697, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4384 p hg
    simpa only [d697, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4386 (p : Pattern) (guard : d0 p = 1) : d461 p ≤ (0 : Int) + d1067 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4387 (p : Pattern) (guard : d4398 p = 1) : d698 p ≤ (0 : Int) + d1114 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d698, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4342 p hg
    simpa only [d4398, d698, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d698, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4386 p hg
    simpa only [d4398, d698, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4388 (p : Pattern) (guard : d4398 p = 1) : d699 p ≤ (0 : Int) + d1115 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d699, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4387 p hg
    simpa only [d699, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d699, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4345 p hg
    simpa only [d699, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4389 (p : Pattern) (guard : d4398 p = 1) : d700 p ≤ (0 : Int) + d1116 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d700, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4385 p hg
    simpa only [d700, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d700, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4388 p hg
    simpa only [d700, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4390 (p : Pattern) (guard : d0 p = 1) : d110 p ≤ (0 : Int) + d450 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4391 (p : Pattern) (guard : d4397 p = 1) : d111 p ≤ (0 : Int) + d1117 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d111, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d4397, d111, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d111, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4390 p hg
    simpa only [d4397, d111, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4392 (p : Pattern) (guard : d4397 p = 1) : d113 p ≤ (0 : Int) + d1118 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d113, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4182 p hg
    simpa only [d4397, d113, d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d113, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d4397, d113, d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4393 (p : Pattern) (guard : d4397 p = 1) : d114 p ≤ (0 : Int) + d1119 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d114, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4391 p hg
    simpa only [d114, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d114, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4392 p hg
    simpa only [d114, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4394 (p : Pattern) (guard : d0 p = 1) : d275 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4395 (p : Pattern) (guard : d4397 p = 1) : d276 p ≤ (0 : Int) + d1120 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d276, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4186 p hg
    simpa only [d4397, d276, d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d276, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4394 p hg
    simpa only [d4397, d276, d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4396 (p : Pattern) (guard : d0 p = 1) : d278 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4397 (p : Pattern) (guard : d4397 p = 1) : d279 p ≤ (0 : Int) + d1121 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d279, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4187 p hg
    simpa only [d4397, d279, d1121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d279, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4396 p hg
    simpa only [d4397, d279, d1121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4398 (p : Pattern) (guard : d4397 p = 1) : d280 p ≤ (0 : Int) + d1122 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d280, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4395 p hg
    simpa only [d280, d1122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d280, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4397 p hg
    simpa only [d280, d1122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4399 (p : Pattern) (guard : d4397 p = 1) : d281 p ≤ (0 : Int) + d1123 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d281, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4393 p hg
    simpa only [d281, d1123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d281, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4398 p hg
    simpa only [d281, d1123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4400 (p : Pattern) (guard : d0 p = 1) : d471 p ≤ (0 : Int) + d1131 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4401 (p : Pattern) (guard : d4398 p = 1) : d701 p ≤ (0 : Int) + d1132 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d701, d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d4398, d701, d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d701, d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d4398, d701, d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4402 (p : Pattern) (guard : d0 p = 1) : d293 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4403 (p : Pattern) (guard : d4397 p = 1) : d294 p ≤ (0 : Int) + d1089 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d294, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4195 p hg
    simpa only [d4397, d294, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d294, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d4397, d294, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4404 (p : Pattern) (guard : d4397 p = 1) : d295 p ≤ (0 : Int) + d1134 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d295, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4199 p hg
    simpa only [d4397, d295, d1134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d295, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4396 p hg
    simpa only [d4397, d295, d1134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4405 (p : Pattern) (guard : d4397 p = 1) : d296 p ≤ (0 : Int) + d1135 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d296, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d296, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d296, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d296, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4406 (p : Pattern) (guard : d4397 p = 1) : d297 p ≤ (0 : Int) + d1136 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d297, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4405 p hg
    simpa only [d297, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d297, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4334 p hg
    simpa only [d297, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4407 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4408 (p : Pattern) (guard : d4398 p = 1) : d702 p ≤ (0 : Int) + d1143 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d702, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4406 p hg
    simpa only [d4398, d702, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d702, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4407 p hg
    simpa only [d4398, d702, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4409 (p : Pattern) (guard : d4398 p = 1) : d703 p ≤ (0 : Int) + d1144 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d703, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d703, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d703, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d703, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4410 (p : Pattern) (guard : d4398 p = 1) : d704 p ≤ (0 : Int) + d1145 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d704, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d704, d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d704, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4278 p hg
    simpa only [d704, d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4411 (p : Pattern) (guard : d4398 p = 1) : d705 p ≤ (0 : Int) + d1146 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d705, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4409 p hg
    simpa only [d705, d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d705, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4410 p hg
    simpa only [d705, d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4412 (p : Pattern) (guard : d4398 p = 1) : d706 p ≤ (0 : Int) + d1147 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d706, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4389 p hg
    simpa only [d706, d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d706, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4411 p hg
    simpa only [d706, d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4413 (p : Pattern) (guard : d4398 p = 1) : d707 p ≤ (0 : Int) + d1148 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d707, d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4281 p hg
    simpa only [d707, d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d707, d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4412 p hg
    simpa only [d707, d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4414 (p : Pattern) (guard : d4398 p = 1) : d708 p ≤ (0 : Int) + d1149 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d708, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4380 p hg
    simpa only [d708, d1149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d708, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4413 p hg
    simpa only [d708, d1149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4415 (p : Pattern) (guard : d4398 p = 1) : d709 p ≤ (0 : Int) + d1150 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d709, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4371 p hg
    simpa only [d709, d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d709, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4414 p hg
    simpa only [d709, d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4416 (p : Pattern) (guard : d1 p = 1) : d267 p ≤ (3 : Int) + d267 p := by
  omega
theorem compare4417 (p : Pattern) (guard : d0 p = 1) : d51 p ≤ (0 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4418 (p : Pattern) (guard : d4117 p = 1) : d52 p ≤ (0 : Int) + d51 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2014 p hg
    simpa only [d4117, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4417 p hg
    simpa only [d4117, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4419 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (0 : Int) + d75 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4420 (p : Pattern) (guard : d4117 p = 1) : d76 p ≤ (0 : Int) + d75 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2029 p hg
    simpa only [d4117, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4419 p hg
    simpa only [d4117, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4421 (p : Pattern) (guard : d4117 p = 1) : d77 p ≤ (0 : Int) + d4120 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d77, d4120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4418 p hg
    simpa only [d77, d4120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d77, d4120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d77, d4120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4422 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1489 p hg
    simpa only [d16, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1999 p hg
    simpa only [d16, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4423 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare824 p hg
    simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4422 p hg
    simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4424 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (0 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4423 p hg
    simpa only [d22, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1528 p hg
    simpa only [d22, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4425 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2007 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4426 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4425 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1527 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4427 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare947 p hg
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4428 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (0 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d29, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4427 p hg
    simpa only [d29, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4429 (p : Pattern) (guard : d0 p = 1) : d81 p ≤ (0 : Int) + d81 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4430 (p : Pattern) (guard : d4117 p = 1) : d82 p ≤ (0 : Int) + d81 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4428 p hg
    simpa only [d4117, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d4117, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4431 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (0 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4422 p hg
    simpa only [d54, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1542 p hg
    simpa only [d54, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4432 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (0 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4431 p hg
    simpa only [d56, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1544 p hg
    simpa only [d56, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4433 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (0 : Int) + d85 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d65, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1547 p hg
    simpa only [d65, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4434 (p : Pattern) (guard : d0 p = 1) : d85 p ≤ (0 : Int) + d85 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4435 (p : Pattern) (guard : d4117 p = 1) : d86 p ≤ (0 : Int) + d85 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4433 p hg
    simpa only [d4117, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4434 p hg
    simpa only [d4117, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4436 (p : Pattern) (guard : d4117 p = 1) : d87 p ≤ (0 : Int) + d4399 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d87, d4399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4430 p hg
    simpa only [d87, d4399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d87, d4399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4435 p hg
    simpa only [d87, d4399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4437 (p : Pattern) (guard : d4117 p = 1) : d88 p ≤ (0 : Int) + d4400 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d88, d4400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4421 p hg
    simpa only [d88, d4400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d88, d4400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d88, d4400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4438 (p : Pattern) (guard : d0 p = 1) : d93 p ≤ (0 : Int) + d93 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4439 (p : Pattern) (guard : d4117 p = 1) : d94 p ≤ (0 : Int) + d93 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1236 p hg
    simpa only [d4117, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4438 p hg
    simpa only [d4117, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4440 (p : Pattern) (guard : d4117 p = 1) : d95 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare765 p hg
    simpa only [d4117, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4117, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4441 (p : Pattern) (guard : d4117 p = 1) : d96 p ≤ (0 : Int) + d4401 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d96, d4401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4439 p hg
    simpa only [d96, d4401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d96, d4401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4440 p hg
    simpa only [d96, d4401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4442 (p : Pattern) (guard : d4117 p = 1) : d97 p ≤ (0 : Int) + d4402 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d97, d4402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d97, d4402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d97, d4402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4441 p hg
    simpa only [d97, d4402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4443 (p : Pattern) (guard : d4117 p = 1) : d98 p ≤ (0 : Int) + d4403 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d98, d4403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4437 p hg
    simpa only [d98, d4403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d98, d4403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4442 p hg
    simpa only [d98, d4403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4444 (p : Pattern) (guard : d4117 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare4445 (p : Pattern) (guard : d4117 p = 1) : d99 p ≤ (0 : Int) + d4404 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d99, d4404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d99, d4404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d99, d4404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d99, d4404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4446 (p : Pattern) (guard : d4117 p = 1) : d100 p ≤ (0 : Int) + d4405 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d100, d4405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4437 p hg
    simpa only [d100, d4405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d100, d4405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4445 p hg
    simpa only [d100, d4405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4447 (p : Pattern) (guard : d4117 p = 1) : d101 p ≤ (0 : Int) + d4406 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d101, d4406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4443 p hg
    simpa only [d101, d4406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d101, d4406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4446 p hg
    simpa only [d101, d4406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4448 (p : Pattern) (guard : d0 p = 1) : d130 p ≤ (0 : Int) + d130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4449 (p : Pattern) (guard : d4117 p = 1) : d131 p ≤ (0 : Int) + d130 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2057 p hg
    simpa only [d4117, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4448 p hg
    simpa only [d4117, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4450 (p : Pattern) (guard : d0 p = 1) : d145 p ≤ (0 : Int) + d145 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4451 (p : Pattern) (guard : d4117 p = 1) : d146 p ≤ (0 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2067 p hg
    simpa only [d4117, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4450 p hg
    simpa only [d4117, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4452 (p : Pattern) (guard : d4117 p = 1) : d147 p ≤ (0 : Int) + d4123 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d147, d4123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4449 p hg
    simpa only [d147, d4123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d147, d4123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4451 p hg
    simpa only [d147, d4123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4453 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1405 p hg
    simpa only [d105, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2047 p hg
    simpa only [d105, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4454 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1251 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4453 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4455 (p : Pattern) (guard : d1 p = 1) : d111 p ≤ (0 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d111, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4454 p hg
    simpa only [d111, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d111, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1591 p hg
    simpa only [d111, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4456 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (0 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d114, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4455 p hg
    simpa only [d114, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d114, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1593 p hg
    simpa only [d114, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4457 (p : Pattern) (guard : d0 p = 1) : d151 p ≤ (0 : Int) + d151 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4458 (p : Pattern) (guard : d4117 p = 1) : d152 p ≤ (0 : Int) + d151 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4456 p hg
    simpa only [d4117, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4457 p hg
    simpa only [d4117, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4459 (p : Pattern) (guard : d1 p = 1) : d133 p ≤ (0 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d133, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4453 p hg
    simpa only [d133, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d133, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1596 p hg
    simpa only [d133, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4460 (p : Pattern) (guard : d1 p = 1) : d135 p ≤ (0 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d135, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4459 p hg
    simpa only [d135, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d135, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1602 p hg
    simpa only [d135, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4461 (p : Pattern) (guard : d1 p = 1) : d138 p ≤ (0 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d138, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d138, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d138, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1605 p hg
    simpa only [d138, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4462 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4463 (p : Pattern) (guard : d4117 p = 1) : d156 p ≤ (0 : Int) + d155 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d4117, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d4117, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4464 (p : Pattern) (guard : d4117 p = 1) : d157 p ≤ (0 : Int) + d4407 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d157, d4407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4458 p hg
    simpa only [d157, d4407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d157, d4407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d157, d4407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4465 (p : Pattern) (guard : d4117 p = 1) : d158 p ≤ (0 : Int) + d4408 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d158, d4408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4452 p hg
    simpa only [d158, d4408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d158, d4408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d158, d4408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4466 (p : Pattern) (guard : d4117 p = 1) : d161 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1308 p hg
    simpa only [d4117, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4117, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4467 (p : Pattern) (guard : d4117 p = 1) : d162 p ≤ (0 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4466 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4468 (p : Pattern) (guard : d4117 p = 1) : d163 p ≤ (0 : Int) + d4409 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d163, d4409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d163, d4409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d163, d4409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4467 p hg
    simpa only [d163, d4409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4469 (p : Pattern) (guard : d4117 p = 1) : d164 p ≤ (0 : Int) + d4410 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d164, d4410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d164, d4410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d164, d4410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4468 p hg
    simpa only [d164, d4410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4470 (p : Pattern) (guard : d4117 p = 1) : d165 p ≤ (0 : Int) + d4409 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d165, d4409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d165, d4409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d165, d4409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d165, d4409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4471 (p : Pattern) (guard : d4117 p = 1) : d166 p ≤ (0 : Int) + d4410 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d166, d4410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d166, d4410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d166, d4410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4470 p hg
    simpa only [d166, d4410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4472 (p : Pattern) (guard : d4117 p = 1) : d167 p ≤ (0 : Int) + d4410 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4471 p hg
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4473 (p : Pattern) (guard : d4117 p = 1) : d168 p ≤ (0 : Int) + d4411 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d168, d4411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d168, d4411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d168, d4411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4472 p hg
    simpa only [d168, d4411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4474 (p : Pattern) (guard : d4117 p = 1) : d169 p ≤ (0 : Int) + d4412 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d169, d4412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d169, d4412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d169, d4412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d169, d4412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4475 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d170 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare781 p hg
    simpa only [d16, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1999 p hg
    simpa only [d16, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4476 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare824 p hg
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4475 p hg
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4477 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d172 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare781 p hg
    simpa only [d16, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1523 p hg
    simpa only [d16, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4478 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (0 : Int) + d173 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare791 p hg
    simpa only [d20, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1526 p hg
    simpa only [d20, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4479 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d174 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d21, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4478 p hg
    simpa only [d21, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
