/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons065
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9240 (p : Pattern) (guard : d4398 p = 1) : d1068 p ≤ (0 : Int) + d681 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1068, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9238 p hg
    simpa only [d4398, d1068, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1068, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9239 p hg
    simpa only [d4398, d1068, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9241 (p : Pattern) (guard : d4398 p = 1) : d1069 p ≤ (0 : Int) + d682 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1069, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9228 p hg
    simpa only [d1069, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1069, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9240 p hg
    simpa only [d1069, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9242 (p : Pattern) (guard : d4397 p = 1) : d1070 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1070, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d4397, d1070, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1070, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7948 p hg
    simpa only [d4397, d1070, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9243 (p : Pattern) (guard : d4397 p = 1) : d1071 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1071, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9242 p hg
    simpa only [d1071, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1071, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9232 p hg
    simpa only [d1071, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9244 (p : Pattern) (guard : d4397 p = 1) : d1072 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1072, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9243 p hg
    simpa only [d1072, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1072, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9237 p hg
    simpa only [d1072, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9245 (p : Pattern) (guard : d0 p = 1) : d1075 p ≤ (0 : Int) + d399 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9246 (p : Pattern) (guard : d4398 p = 1) : d1076 p ≤ (0 : Int) + d683 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1076, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9244 p hg
    simpa only [d4398, d1076, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1076, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9245 p hg
    simpa only [d4398, d1076, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9247 (p : Pattern) (guard : d4398 p = 1) : d1077 p ≤ (0 : Int) + d684 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1077, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9246 p hg
    simpa only [d1077, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1077, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4345 p hg
    simpa only [d1077, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9248 (p : Pattern) (guard : d4398 p = 1) : d1078 p ≤ (0 : Int) + d685 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1078, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9241 p hg
    simpa only [d1078, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1078, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9247 p hg
    simpa only [d1078, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9249 (p : Pattern) (guard : d4397 p = 1) : d1079 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1079, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d4397, d1079, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1079, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7960 p hg
    simpa only [d4397, d1079, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9250 (p : Pattern) (guard : d4397 p = 1) : d1080 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1080, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9218 p hg
    simpa only [d4397, d1080, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1080, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d4397, d1080, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9251 (p : Pattern) (guard : d4397 p = 1) : d1081 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1081, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9249 p hg
    simpa only [d1081, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1081, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9250 p hg
    simpa only [d1081, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9252 (p : Pattern) (guard : d4397 p = 1) : d1082 p ≤ (0 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1082, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9222 p hg
    simpa only [d4397, d1082, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1082, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7964 p hg
    simpa only [d4397, d1082, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9253 (p : Pattern) (guard : d4397 p = 1) : d1083 p ≤ (0 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1083, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9252 p hg
    simpa only [d1083, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1083, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9224 p hg
    simpa only [d1083, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9254 (p : Pattern) (guard : d4397 p = 1) : d1084 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1084, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9251 p hg
    simpa only [d1084, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1084, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9253 p hg
    simpa only [d1084, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9255 (p : Pattern) (guard : d0 p = 1) : d1087 p ≤ (0 : Int) + d407 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9256 (p : Pattern) (guard : d4398 p = 1) : d1088 p ≤ (0 : Int) + d686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1088, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9254 p hg
    simpa only [d4398, d1088, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1088, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9255 p hg
    simpa only [d4398, d1088, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9257 (p : Pattern) (guard : d4397 p = 1) : d1089 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1089, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d4397, d1089, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1089, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7973 p hg
    simpa only [d4397, d1089, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9258 (p : Pattern) (guard : d4397 p = 1) : d1090 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1090, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9257 p hg
    simpa only [d1090, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1090, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9232 p hg
    simpa only [d1090, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9259 (p : Pattern) (guard : d4397 p = 1) : d1091 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1091, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9258 p hg
    simpa only [d1091, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1091, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9237 p hg
    simpa only [d1091, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9260 (p : Pattern) (guard : d0 p = 1) : d1067 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9261 (p : Pattern) (guard : d4398 p = 1) : d1092 p ≤ (0 : Int) + d687 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1092, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9259 p hg
    simpa only [d4398, d1092, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1092, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9260 p hg
    simpa only [d4398, d1092, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9262 (p : Pattern) (guard : d4398 p = 1) : d1093 p ≤ (0 : Int) + d688 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1093, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9256 p hg
    simpa only [d1093, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1093, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9261 p hg
    simpa only [d1093, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9263 (p : Pattern) (guard : d0 p = 1) : d1067 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9264 (p : Pattern) (guard : d4398 p = 1) : d1092 p ≤ (0 : Int) + d689 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1092, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9259 p hg
    simpa only [d4398, d1092, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1092, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9263 p hg
    simpa only [d4398, d1092, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9265 (p : Pattern) (guard : d4398 p = 1) : d1094 p ≤ (0 : Int) + d690 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1094, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9264 p hg
    simpa only [d1094, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1094, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4278 p hg
    simpa only [d1094, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9266 (p : Pattern) (guard : d4398 p = 1) : d1095 p ≤ (0 : Int) + d691 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1095, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9262 p hg
    simpa only [d1095, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1095, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9265 p hg
    simpa only [d1095, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9267 (p : Pattern) (guard : d4398 p = 1) : d1096 p ≤ (0 : Int) + d692 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1096, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9248 p hg
    simpa only [d1096, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1096, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9266 p hg
    simpa only [d1096, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9268 (p : Pattern) (guard : d4398 p = 1) : d1097 p ≤ (0 : Int) + d693 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1097, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9187 p hg
    simpa only [d1097, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1097, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9267 p hg
    simpa only [d1097, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9269 (p : Pattern) (guard : d4398 p = 1) : d1098 p ≤ (0 : Int) + d694 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1098, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9215 p hg
    simpa only [d1098, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1098, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9268 p hg
    simpa only [d1098, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9270 (p : Pattern) (guard : d0 p = 1) : d1102 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9271 (p : Pattern) (guard : d4398 p = 1) : d1103 p ≤ (0 : Int) + d674 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1103, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9176 p hg
    simpa only [d4398, d1103, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1103, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9270 p hg
    simpa only [d4398, d1103, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9272 (p : Pattern) (guard : d4398 p = 1) : d1104 p ≤ (0 : Int) + d675 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1104, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9208 p hg
    simpa only [d1104, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1104, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9271 p hg
    simpa only [d1104, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9273 (p : Pattern) (guard : d0 p = 1) : d1102 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9274 (p : Pattern) (guard : d4398 p = 1) : d1103 p ≤ (0 : Int) + d661 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1103, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9176 p hg
    simpa only [d4398, d1103, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1103, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9273 p hg
    simpa only [d4398, d1103, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9275 (p : Pattern) (guard : d4398 p = 1) : d1105 p ≤ (0 : Int) + d676 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1105, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9274 p hg
    simpa only [d1105, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1105, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4278 p hg
    simpa only [d1105, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9276 (p : Pattern) (guard : d4398 p = 1) : d1106 p ≤ (0 : Int) + d677 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1106, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9272 p hg
    simpa only [d1106, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1106, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9275 p hg
    simpa only [d1106, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9277 (p : Pattern) (guard : d4398 p = 1) : d1107 p ≤ (0 : Int) + d678 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1107, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9204 p hg
    simpa only [d1107, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1107, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9276 p hg
    simpa only [d1107, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9278 (p : Pattern) (guard : d4398 p = 1) : d1108 p ≤ (0 : Int) + d679 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1108, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9187 p hg
    simpa only [d1108, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1108, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9277 p hg
    simpa only [d1108, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9279 (p : Pattern) (guard : d0 p = 1) : d1111 p ≤ (0 : Int) + d453 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9280 (p : Pattern) (guard : d4398 p = 1) : d1112 p ≤ (0 : Int) + d695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1112, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9226 p hg
    simpa only [d4398, d1112, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1112, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9279 p hg
    simpa only [d4398, d1112, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9281 (p : Pattern) (guard : d0 p = 1) : d1067 p ≤ (0 : Int) + d456 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9282 (p : Pattern) (guard : d4398 p = 1) : d1068 p ≤ (0 : Int) + d696 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1068, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9238 p hg
    simpa only [d4398, d1068, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1068, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9281 p hg
    simpa only [d4398, d1068, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9283 (p : Pattern) (guard : d4398 p = 1) : d1113 p ≤ (0 : Int) + d697 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1113, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9280 p hg
    simpa only [d1113, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1113, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9282 p hg
    simpa only [d1113, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9284 (p : Pattern) (guard : d0 p = 1) : d1067 p ≤ (0 : Int) + d461 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9285 (p : Pattern) (guard : d4398 p = 1) : d1114 p ≤ (0 : Int) + d698 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1114, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9244 p hg
    simpa only [d4398, d1114, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1114, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9284 p hg
    simpa only [d4398, d1114, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9286 (p : Pattern) (guard : d4398 p = 1) : d1115 p ≤ (0 : Int) + d699 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1115, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9285 p hg
    simpa only [d1115, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1115, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4345 p hg
    simpa only [d1115, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9287 (p : Pattern) (guard : d4398 p = 1) : d1116 p ≤ (0 : Int) + d700 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1116, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9283 p hg
    simpa only [d1116, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1116, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9286 p hg
    simpa only [d1116, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9288 (p : Pattern) (guard : d4397 p = 1) : d1117 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1117, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d4397, d1117, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1117, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8003 p hg
    simpa only [d4397, d1117, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9289 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (0 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9290 (p : Pattern) (guard : d4148 p = 1) : d291 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d291, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d291, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d291, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9289 p hg
    simpa only [d4148, d291, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9291 (p : Pattern) (guard : d4397 p = 1) : d1118 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1118, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9290 p hg
    simpa only [d4397, d1118, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1118, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d4397, d1118, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9292 (p : Pattern) (guard : d4397 p = 1) : d1119 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1119, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9288 p hg
    simpa only [d1119, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1119, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9291 p hg
    simpa only [d1119, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9293 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (0 : Int) + d270 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9294 (p : Pattern) (guard : d4148 p = 1) : d269 p ≤ (0 : Int) + d271 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4148, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9293 p hg
    simpa only [d4148, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9295 (p : Pattern) (guard : d4397 p = 1) : d1120 p ≤ (0 : Int) + d276 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1120, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9294 p hg
    simpa only [d4397, d1120, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1120, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8008 p hg
    simpa only [d4397, d1120, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9296 (p : Pattern) (guard : d4397 p = 1) : d1121 p ≤ (0 : Int) + d279 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1121, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4187 p hg
    simpa only [d4397, d1121, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1121, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8011 p hg
    simpa only [d4397, d1121, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9297 (p : Pattern) (guard : d4397 p = 1) : d1122 p ≤ (0 : Int) + d280 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1122, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9295 p hg
    simpa only [d1122, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1122, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9296 p hg
    simpa only [d1122, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9298 (p : Pattern) (guard : d4397 p = 1) : d1123 p ≤ (0 : Int) + d281 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1123, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9292 p hg
    simpa only [d1123, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1123, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9297 p hg
    simpa only [d1123, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9299 (p : Pattern) (guard : d0 p = 1) : d1131 p ≤ (0 : Int) + d471 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9300 (p : Pattern) (guard : d4398 p = 1) : d1132 p ≤ (0 : Int) + d701 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1132, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9298 p hg
    simpa only [d4398, d1132, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1132, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9299 p hg
    simpa only [d4398, d1132, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9301 (p : Pattern) (guard : d0 p = 1) : d105 p ≤ (0 : Int) + d269 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9302 (p : Pattern) (guard : d4148 p = 1) : d105 p ≤ (0 : Int) + d291 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9301 p hg
    simpa only [d4148, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9303 (p : Pattern) (guard : d4397 p = 1) : d1089 p ≤ (0 : Int) + d294 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1089, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9302 p hg
    simpa only [d4397, d1089, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1089, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8023 p hg
    simpa only [d4397, d1089, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9304 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (0 : Int) + d292 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9305 (p : Pattern) (guard : d4148 p = 1) : d1133 p ≤ (0 : Int) + d293 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1133, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4148, d1133, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1133, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9304 p hg
    simpa only [d4148, d1133, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9306 (p : Pattern) (guard : d4397 p = 1) : d1134 p ≤ (0 : Int) + d295 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1134, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9305 p hg
    simpa only [d4397, d1134, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1134, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8011 p hg
    simpa only [d4397, d1134, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9307 (p : Pattern) (guard : d4397 p = 1) : d1135 p ≤ (0 : Int) + d296 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1135, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9303 p hg
    simpa only [d1135, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1135, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9306 p hg
    simpa only [d1135, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9308 (p : Pattern) (guard : d4397 p = 1) : d1136 p ≤ (0 : Int) + d297 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1136, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9307 p hg
    simpa only [d1136, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1136, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9237 p hg
    simpa only [d1136, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9309 (p : Pattern) (guard : d0 p = 1) : d1142 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9310 (p : Pattern) (guard : d4398 p = 1) : d1143 p ≤ (0 : Int) + d702 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1143, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9308 p hg
    simpa only [d4398, d1143, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1143, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9309 p hg
    simpa only [d4398, d1143, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9311 (p : Pattern) (guard : d4398 p = 1) : d1144 p ≤ (0 : Int) + d703 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1144, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9300 p hg
    simpa only [d1144, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1144, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9310 p hg
    simpa only [d1144, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9312 (p : Pattern) (guard : d4398 p = 1) : d1145 p ≤ (0 : Int) + d704 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1145, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9310 p hg
    simpa only [d1145, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1145, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4278 p hg
    simpa only [d1145, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9313 (p : Pattern) (guard : d4398 p = 1) : d1146 p ≤ (0 : Int) + d705 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1146, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9311 p hg
    simpa only [d1146, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1146, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9312 p hg
    simpa only [d1146, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9314 (p : Pattern) (guard : d4398 p = 1) : d1147 p ≤ (0 : Int) + d706 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1147, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9287 p hg
    simpa only [d1147, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1147, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9313 p hg
    simpa only [d1147, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9315 (p : Pattern) (guard : d4398 p = 1) : d1148 p ≤ (0 : Int) + d707 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1148, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9187 p hg
    simpa only [d1148, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1148, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9314 p hg
    simpa only [d1148, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9316 (p : Pattern) (guard : d4398 p = 1) : d1149 p ≤ (0 : Int) + d708 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1149, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9278 p hg
    simpa only [d1149, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1149, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9315 p hg
    simpa only [d1149, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9317 (p : Pattern) (guard : d4398 p = 1) : d1150 p ≤ (0 : Int) + d709 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1150, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9269 p hg
    simpa only [d1150, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1150, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9316 p hg
    simpa only [d1150, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9318 (p : Pattern) (guard : d0 p = 1) : d337 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9319 (p : Pattern) (guard : d4148 p = 1) : d1151 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9318 p hg
    simpa only [d4148, d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9320 (p : Pattern) (guard : d0 p = 1) : d345 p ≤ (0 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9321 (p : Pattern) (guard : d4148 p = 1) : d1152 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1152, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1152, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1152, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9320 p hg
    simpa only [d4148, d1152, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9322 (p : Pattern) (guard : d4148 p = 1) : d1153 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1153, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9319 p hg
    simpa only [d1153, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1153, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9321 p hg
    simpa only [d1153, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9323 (p : Pattern) (guard : d0 p = 1) : d354 p ≤ (0 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9324 (p : Pattern) (guard : d4148 p = 1) : d1154 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1154, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1154, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1154, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9323 p hg
    simpa only [d4148, d1154, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9325 (p : Pattern) (guard : d4148 p = 1) : d1155 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1155, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9324 p hg
    simpa only [d1155, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1155, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1155, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9326 (p : Pattern) (guard : d4148 p = 1) : d1156 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1156, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9322 p hg
    simpa only [d1156, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1156, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9325 p hg
    simpa only [d1156, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9327 (p : Pattern) (guard : d0 p = 1) : d360 p ≤ (0 : Int) + d37 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9328 (p : Pattern) (guard : d4148 p = 1) : d1157 p ≤ (0 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1157, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4148, d1157, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1157, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9327 p hg
    simpa only [d4148, d1157, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9329 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d43 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9330 (p : Pattern) (guard : d4148 p = 1) : d1158 p ≤ (0 : Int) + d44 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1158, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3626 p hg
    simpa only [d4148, d1158, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1158, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9329 p hg
    simpa only [d4148, d1158, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9331 (p : Pattern) (guard : d4148 p = 1) : d1159 p ≤ (0 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1159, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9328 p hg
    simpa only [d1159, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1159, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9330 p hg
    simpa only [d1159, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9332 (p : Pattern) (guard : d4148 p = 1) : d1160 p ≤ (0 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1160, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3630 p hg
    simpa only [d4148, d1160, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1160, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9329 p hg
    simpa only [d4148, d1160, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9333 (p : Pattern) (guard : d4148 p = 1) : d1161 p ≤ (0 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1161, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9332 p hg
    simpa only [d1161, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1161, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3632 p hg
    simpa only [d1161, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9334 (p : Pattern) (guard : d4148 p = 1) : d1162 p ≤ (0 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1162, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9331 p hg
    simpa only [d1162, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1162, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9333 p hg
    simpa only [d1162, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9335 (p : Pattern) (guard : d4148 p = 1) : d1163 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1163, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9326 p hg
    simpa only [d1163, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1163, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9334 p hg
    simpa only [d1163, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9336 (p : Pattern) (guard : d0 p = 1) : d1175 p ≤ (0 : Int) + d392 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9337 (p : Pattern) (guard : d4303 p = 1) : d1176 p ≤ (0 : Int) + d653 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1176, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9335 p hg
    simpa only [d4303, d1176, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1176, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9336 p hg
    simpa only [d4303, d1176, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9338 (p : Pattern) (guard : d0 p = 1) : d354 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9339 (p : Pattern) (guard : d4148 p = 1) : d1154 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9338 p hg
    simpa only [d4148, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9340 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9341 (p : Pattern) (guard : d4148 p = 1) : d1177 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1177, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1177, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1177, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9340 p hg
    simpa only [d4148, d1177, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9342 (p : Pattern) (guard : d4148 p = 1) : d1178 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1178, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9339 p hg
    simpa only [d1178, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1178, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9341 p hg
    simpa only [d1178, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9343 (p : Pattern) (guard : d4148 p = 1) : d1179 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1179, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9341 p hg
    simpa only [d1179, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1179, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1179, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9344 (p : Pattern) (guard : d4148 p = 1) : d1180 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1180, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9342 p hg
    simpa only [d1180, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1180, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9343 p hg
    simpa only [d1180, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9345 (p : Pattern) (guard : d4148 p = 1) : d1181 p ≤ (0 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1181, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4148, d1181, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1181, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2346 p hg
    simpa only [d4148, d1181, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9346 (p : Pattern) (guard : d4148 p = 1) : d1182 p ≤ (0 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1182, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9345 p hg
    simpa only [d1182, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1182, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d1182, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9347 (p : Pattern) (guard : d4148 p = 1) : d1183 p ≤ (0 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1183, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9346 p hg
    simpa only [d1183, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1183, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1183, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9348 (p : Pattern) (guard : d4148 p = 1) : d1184 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1184, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9344 p hg
    simpa only [d1184, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1184, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9347 p hg
    simpa only [d1184, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9349 (p : Pattern) (guard : d0 p = 1) : d1190 p ≤ (0 : Int) + d399 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9350 (p : Pattern) (guard : d4303 p = 1) : d1191 p ≤ (0 : Int) + d654 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1191, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9348 p hg
    simpa only [d4303, d1191, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1191, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9349 p hg
    simpa only [d4303, d1191, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9351 (p : Pattern) (guard : d4303 p = 1) : d1192 p ≤ (0 : Int) + d655 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1192, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9337 p hg
    simpa only [d1192, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1192, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9350 p hg
    simpa only [d1192, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9352 (p : Pattern) (guard : d0 p = 1) : d345 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9353 (p : Pattern) (guard : d4148 p = 1) : d1152 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9352 p hg
    simpa only [d4148, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9354 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (0 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9355 (p : Pattern) (guard : d4148 p = 1) : d1193 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1193, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1193, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1193, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9354 p hg
    simpa only [d4148, d1193, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9356 (p : Pattern) (guard : d4148 p = 1) : d1194 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1194, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9353 p hg
    simpa only [d1194, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1194, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9355 p hg
    simpa only [d1194, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9357 (p : Pattern) (guard : d4148 p = 1) : d1195 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1195, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9356 p hg
    simpa only [d1195, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1195, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9343 p hg
    simpa only [d1195, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9358 (p : Pattern) (guard : d4148 p = 1) : d1196 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1196, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9357 p hg
    simpa only [d1196, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1196, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9347 p hg
    simpa only [d1196, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9359 (p : Pattern) (guard : d0 p = 1) : d1200 p ≤ (0 : Int) + d407 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9360 (p : Pattern) (guard : d4303 p = 1) : d1201 p ≤ (0 : Int) + d656 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1201, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9358 p hg
    simpa only [d4303, d1201, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1201, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9359 p hg
    simpa only [d4303, d1201, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9361 (p : Pattern) (guard : d4148 p = 1) : d27 p ≤ (0 : Int) + d89 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d27, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3663 p hg
    simpa only [d4148, d27, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d27, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2356 p hg
    simpa only [d4148, d27, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9362 (p : Pattern) (guard : d4148 p = 1) : d1202 p ≤ (0 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1202, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9361 p hg
    simpa only [d1202, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1202, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d1202, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9363 (p : Pattern) (guard : d4148 p = 1) : d1203 p ≤ (0 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1203, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9362 p hg
    simpa only [d1203, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1203, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3667 p hg
    simpa only [d1203, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9364 (p : Pattern) (guard : d4148 p = 1) : d1204 p ≤ (0 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1204, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9363 p hg
    simpa only [d1204, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1204, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3669 p hg
    simpa only [d1204, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9365 (p : Pattern) (guard : d4303 p = 1) : d1205 p ≤ (0 : Int) + d657 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1205, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9364 p hg
    simpa only [d4303, d1205, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1205, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2241 p hg
    simpa only [d4303, d1205, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9366 (p : Pattern) (guard : d4303 p = 1) : d1206 p ≤ (0 : Int) + d658 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1206, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9360 p hg
    simpa only [d1206, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1206, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9365 p hg
    simpa only [d1206, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9367 (p : Pattern) (guard : d4303 p = 1) : d1207 p ≤ (0 : Int) + d659 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1207, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9351 p hg
    simpa only [d1207, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1207, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9366 p hg
    simpa only [d1207, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9368 (p : Pattern) (guard : d0 p = 1) : d368 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9369 (p : Pattern) (guard : d4148 p = 1) : d1208 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9368 p hg
    simpa only [d4148, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9370 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (0 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9371 (p : Pattern) (guard : d4148 p = 1) : d1185 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1185, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1185, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1185, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9370 p hg
    simpa only [d4148, d1185, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9372 (p : Pattern) (guard : d4148 p = 1) : d1209 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1209, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9369 p hg
    simpa only [d1209, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1209, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9371 p hg
    simpa only [d1209, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9373 (p : Pattern) (guard : d4148 p = 1) : d1210 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1210, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9355 p hg
    simpa only [d1210, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1210, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1210, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9374 (p : Pattern) (guard : d4148 p = 1) : d1211 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1211, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9372 p hg
    simpa only [d1211, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1211, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9373 p hg
    simpa only [d1211, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9375 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d37 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9376 (p : Pattern) (guard : d4148 p = 1) : d1212 p ≤ (0 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1212, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4148, d1212, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1212, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9375 p hg
    simpa only [d4148, d1212, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9377 (p : Pattern) (guard : d4148 p = 1) : d1213 p ≤ (0 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1213, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9376 p hg
    simpa only [d1213, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1213, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9330 p hg
    simpa only [d1213, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9378 (p : Pattern) (guard : d4148 p = 1) : d1214 p ≤ (0 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1214, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9377 p hg
    simpa only [d1214, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1214, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9333 p hg
    simpa only [d1214, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9379 (p : Pattern) (guard : d4148 p = 1) : d1215 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1215, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9374 p hg
    simpa only [d1215, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1215, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9378 p hg
    simpa only [d1215, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
