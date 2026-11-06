/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons037
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5320 (p : Pattern) (guard : d1174 p = 1) : d616 p ≤ (0 : Int) + d1067 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d616, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5314 p hg
    simpa only [d616, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d616, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5319 p hg
    simpa only [d616, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5321 (p : Pattern) (guard : d1174 p = 1) : d617 p ≤ (0 : Int) + d1068 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d617, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5312 p hg
    simpa only [d617, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d617, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5320 p hg
    simpa only [d617, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5322 (p : Pattern) (guard : d1174 p = 1) : d618 p ≤ (0 : Int) + d1069 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d618, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5302 p hg
    simpa only [d618, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d618, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5321 p hg
    simpa only [d618, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5323 (p : Pattern) (guard : d1174 p = 1) : d619 p ≤ (0 : Int) + d48 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d619, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5293 p hg
    simpa only [d619, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d619, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5303 p hg
    simpa only [d619, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5324 (p : Pattern) (guard : d1174 p = 1) : d620 p ≤ (0 : Int) + d1070 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d620, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5301 p hg
    simpa only [d620, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d620, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5313 p hg
    simpa only [d620, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5325 (p : Pattern) (guard : d1174 p = 1) : d621 p ≤ (0 : Int) + d1071 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d621, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5323 p hg
    simpa only [d621, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d621, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5324 p hg
    simpa only [d621, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5326 (p : Pattern) (guard : d1174 p = 1) : d622 p ≤ (0 : Int) + d164 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d622, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5311 p hg
    simpa only [d622, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d622, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5303 p hg
    simpa only [d622, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5327 (p : Pattern) (guard : d1174 p = 1) : d623 p ≤ (0 : Int) + d1072 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d623, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5319 p hg
    simpa only [d623, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d623, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5313 p hg
    simpa only [d623, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5328 (p : Pattern) (guard : d1174 p = 1) : d624 p ≤ (0 : Int) + d1073 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d624, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5326 p hg
    simpa only [d624, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d624, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5327 p hg
    simpa only [d624, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5329 (p : Pattern) (guard : d1174 p = 1) : d625 p ≤ (0 : Int) + d1074 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d625, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5325 p hg
    simpa only [d625, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d625, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5328 p hg
    simpa only [d625, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5330 (p : Pattern) (guard : d1174 p = 1) : d626 p ≤ (0 : Int) + d1075 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d626, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5322 p hg
    simpa only [d626, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d626, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5329 p hg
    simpa only [d626, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5331 (p : Pattern) (guard : d1174 p = 1) : d627 p ≤ (0 : Int) + d1076 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d627, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5303 p hg
    simpa only [d627, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d627, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5313 p hg
    simpa only [d627, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5332 (p : Pattern) (guard : d1174 p = 1) : d628 p ≤ (0 : Int) + d1077 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d628, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5329 p hg
    simpa only [d628, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d628, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5331 p hg
    simpa only [d628, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5333 (p : Pattern) (guard : d1174 p = 1) : d629 p ≤ (0 : Int) + d1078 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d629, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5330 p hg
    simpa only [d629, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d629, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5332 p hg
    simpa only [d629, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5334 (p : Pattern) (guard : d1174 p = 1) : d630 p ≤ (0 : Int) + d92 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d630, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5305 p hg
    simpa only [d630, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d630, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5287 p hg
    simpa only [d630, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5335 (p : Pattern) (guard : d1174 p = 1) : d631 p ≤ (0 : Int) + d92 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d631, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5307 p hg
    simpa only [d631, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d631, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5290 p hg
    simpa only [d631, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5336 (p : Pattern) (guard : d1174 p = 1) : d632 p ≤ (0 : Int) + d92 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5334 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5335 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5337 (p : Pattern) (guard : d1174 p = 1) : d633 p ≤ (0 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d633, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5309 p hg
    simpa only [d633, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d633, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5336 p hg
    simpa only [d633, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5338 (p : Pattern) (guard : d1174 p = 1) : d634 p ≤ (0 : Int) + d100 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d634, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5293 p hg
    simpa only [d634, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d634, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5337 p hg
    simpa only [d634, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5339 (p : Pattern) (guard : d1174 p = 1) : d635 p ≤ (0 : Int) + d169 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d635, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5293 p hg
    simpa only [d635, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d635, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5338 p hg
    simpa only [d635, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5340 (p : Pattern) (guard : d1174 p = 1) : d636 p ≤ (0 : Int) + d1079 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d636, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5315 p hg
    simpa only [d636, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d636, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5298 p hg
    simpa only [d636, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5341 (p : Pattern) (guard : d1174 p = 1) : d637 p ≤ (0 : Int) + d1080 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d637, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5335 p hg
    simpa only [d637, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d637, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5340 p hg
    simpa only [d637, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5342 (p : Pattern) (guard : d1174 p = 1) : d638 p ≤ (0 : Int) + d1081 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d638, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5317 p hg
    simpa only [d638, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d638, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5341 p hg
    simpa only [d638, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5343 (p : Pattern) (guard : d1174 p = 1) : d639 p ≤ (0 : Int) + d1082 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d639, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5301 p hg
    simpa only [d639, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d639, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5342 p hg
    simpa only [d639, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5344 (p : Pattern) (guard : d1174 p = 1) : d640 p ≤ (0 : Int) + d1083 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d640, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5301 p hg
    simpa only [d640, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d640, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5343 p hg
    simpa only [d640, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5345 (p : Pattern) (guard : d1174 p = 1) : d641 p ≤ (0 : Int) + d1084 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d641, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5339 p hg
    simpa only [d641, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d641, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5344 p hg
    simpa only [d641, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5346 (p : Pattern) (guard : d1174 p = 1) : d642 p ≤ (0 : Int) + d1085 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d642, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5345 p hg
    simpa only [d642, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d642, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5331 p hg
    simpa only [d642, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5347 (p : Pattern) (guard : d1174 p = 1) : d643 p ≤ (0 : Int) + d93 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d643, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5283 p hg
    simpa only [d643, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d643, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5336 p hg
    simpa only [d643, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5348 (p : Pattern) (guard : d1174 p = 1) : d644 p ≤ (0 : Int) + d95 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d644, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5347 p hg
    simpa only [d644, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d644, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5337 p hg
    simpa only [d644, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5349 (p : Pattern) (guard : d1174 p = 1) : d645 p ≤ (0 : Int) + d171 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d645, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5348 p hg
    simpa only [d645, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d645, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5303 p hg
    simpa only [d645, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5350 (p : Pattern) (guard : d1174 p = 1) : d646 p ≤ (0 : Int) + d1086 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d646, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5296 p hg
    simpa only [d646, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d646, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5341 p hg
    simpa only [d646, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5351 (p : Pattern) (guard : d1174 p = 1) : d647 p ≤ (0 : Int) + d1087 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d647, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5350 p hg
    simpa only [d647, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d647, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5342 p hg
    simpa only [d647, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5352 (p : Pattern) (guard : d1174 p = 1) : d648 p ≤ (0 : Int) + d1088 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d648, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5351 p hg
    simpa only [d648, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d648, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5313 p hg
    simpa only [d648, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5353 (p : Pattern) (guard : d1174 p = 1) : d649 p ≤ (0 : Int) + d1089 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d649, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5349 p hg
    simpa only [d649, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d649, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5352 p hg
    simpa only [d649, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5354 (p : Pattern) (guard : d1174 p = 1) : d650 p ≤ (0 : Int) + d1090 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d650, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5353 p hg
    simpa only [d650, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d650, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5331 p hg
    simpa only [d650, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5355 (p : Pattern) (guard : d1174 p = 1) : d651 p ≤ (0 : Int) + d1091 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d651, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5346 p hg
    simpa only [d651, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d651, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5354 p hg
    simpa only [d651, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5356 (p : Pattern) (guard : d1174 p = 1) : d652 p ≤ (0 : Int) + d174 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d652, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5338 p hg
    simpa only [d652, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d652, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5303 p hg
    simpa only [d652, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5357 (p : Pattern) (guard : d1174 p = 1) : d653 p ≤ (0 : Int) + d1092 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d653, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5343 p hg
    simpa only [d653, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d653, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5313 p hg
    simpa only [d653, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5358 (p : Pattern) (guard : d1174 p = 1) : d654 p ≤ (0 : Int) + d1093 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d654, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5356 p hg
    simpa only [d654, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d654, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5357 p hg
    simpa only [d654, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5359 (p : Pattern) (guard : d1174 p = 1) : d655 p ≤ (0 : Int) + d1094 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d655, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5358 p hg
    simpa only [d655, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d655, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5331 p hg
    simpa only [d655, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5360 (p : Pattern) (guard : d1174 p = 1) : d656 p ≤ (0 : Int) + d1095 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d656, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5359 p hg
    simpa only [d656, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d656, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5331 p hg
    simpa only [d656, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5361 (p : Pattern) (guard : d1174 p = 1) : d657 p ≤ (0 : Int) + d1096 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d657, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5355 p hg
    simpa only [d657, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d657, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5360 p hg
    simpa only [d657, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5362 (p : Pattern) (guard : d1174 p = 1) : d658 p ≤ (0 : Int) + d1097 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d658, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5333 p hg
    simpa only [d658, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d658, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5361 p hg
    simpa only [d658, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5363 (p : Pattern) (guard : d0 p = 1) : d30 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5364 (p : Pattern) (guard : d1134 p = 1) : d31 p ≤ (0 : Int) + d21 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d31, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4956 p hg
    simpa only [d1134, d31, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d31, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5363 p hg
    simpa only [d1134, d31, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5365 (p : Pattern) (guard : d0 p = 1) : d591 p ≤ (0 : Int) + d261 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5366 (p : Pattern) (guard : d1134 p = 1) : d592 p ≤ (0 : Int) + d375 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d592, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4966 p hg
    simpa only [d1134, d592, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d592, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5365 p hg
    simpa only [d1134, d592, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5367 (p : Pattern) (guard : d1134 p = 1) : d593 p ≤ (0 : Int) + d376 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d593, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5364 p hg
    simpa only [d593, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d593, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5366 p hg
    simpa only [d593, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5368 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (0 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5369 (p : Pattern) (guard : d1134 p = 1) : d33 p ≤ (0 : Int) + d22 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d33, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4959 p hg
    simpa only [d1134, d33, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d33, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5368 p hg
    simpa only [d1134, d33, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5370 (p : Pattern) (guard : d0 p = 1) : d595 p ≤ (0 : Int) + d265 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5371 (p : Pattern) (guard : d1134 p = 1) : d596 p ≤ (0 : Int) + d377 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d596, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4970 p hg
    simpa only [d1134, d596, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d596, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5370 p hg
    simpa only [d1134, d596, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5372 (p : Pattern) (guard : d1134 p = 1) : d597 p ≤ (0 : Int) + d378 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d597, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5369 p hg
    simpa only [d597, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d597, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5371 p hg
    simpa only [d597, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5373 (p : Pattern) (guard : d1134 p = 1) : d598 p ≤ (0 : Int) + d379 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d598, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5367 p hg
    simpa only [d598, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d598, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5372 p hg
    simpa only [d598, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5374 (p : Pattern) (guard : d0 p = 1) : d590 p ≤ (0 : Int) + d260 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5375 (p : Pattern) (guard : d1134 p = 1) : d599 p ≤ (0 : Int) + d380 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d599, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4965 p hg
    simpa only [d1134, d599, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d599, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5374 p hg
    simpa only [d1134, d599, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5376 (p : Pattern) (guard : d1134 p = 1) : d600 p ≤ (0 : Int) + d381 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d600, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5364 p hg
    simpa only [d600, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d600, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5375 p hg
    simpa only [d600, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5377 (p : Pattern) (guard : d0 p = 1) : d604 p ≤ (0 : Int) + d272 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5378 (p : Pattern) (guard : d1134 p = 1) : d605 p ≤ (0 : Int) + d382 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d605, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4991 p hg
    simpa only [d1134, d605, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d605, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5377 p hg
    simpa only [d1134, d605, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5379 (p : Pattern) (guard : d1134 p = 1) : d606 p ≤ (0 : Int) + d383 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d606, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5378 p hg
    simpa only [d606, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d606, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5375 p hg
    simpa only [d606, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5380 (p : Pattern) (guard : d1134 p = 1) : d607 p ≤ (0 : Int) + d384 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d607, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5376 p hg
    simpa only [d607, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d607, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5379 p hg
    simpa only [d607, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5381 (p : Pattern) (guard : d1134 p = 1) : d608 p ≤ (0 : Int) + d385 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d608, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5376 p hg
    simpa only [d608, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d608, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5380 p hg
    simpa only [d608, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5382 (p : Pattern) (guard : d0 p = 1) : d594 p ≤ (0 : Int) + d264 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5383 (p : Pattern) (guard : d1134 p = 1) : d609 p ≤ (0 : Int) + d386 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d609, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4969 p hg
    simpa only [d1134, d609, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d609, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5382 p hg
    simpa only [d1134, d609, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5384 (p : Pattern) (guard : d1134 p = 1) : d610 p ≤ (0 : Int) + d387 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d610, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5369 p hg
    simpa only [d610, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d610, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5383 p hg
    simpa only [d610, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5385 (p : Pattern) (guard : d0 p = 1) : d612 p ≤ (0 : Int) + d274 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5386 (p : Pattern) (guard : d1134 p = 1) : d613 p ≤ (0 : Int) + d388 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d613, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d1134, d613, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d613, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5385 p hg
    simpa only [d1134, d613, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5387 (p : Pattern) (guard : d1134 p = 1) : d614 p ≤ (0 : Int) + d389 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d614, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5386 p hg
    simpa only [d614, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d614, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5383 p hg
    simpa only [d614, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5388 (p : Pattern) (guard : d1134 p = 1) : d615 p ≤ (0 : Int) + d390 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d615, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5384 p hg
    simpa only [d615, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d615, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5387 p hg
    simpa only [d615, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5389 (p : Pattern) (guard : d1134 p = 1) : d616 p ≤ (0 : Int) + d391 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d616, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5384 p hg
    simpa only [d616, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d616, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5388 p hg
    simpa only [d616, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5390 (p : Pattern) (guard : d1134 p = 1) : d617 p ≤ (0 : Int) + d392 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d617, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5381 p hg
    simpa only [d617, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d617, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5389 p hg
    simpa only [d617, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5391 (p : Pattern) (guard : d1134 p = 1) : d618 p ≤ (0 : Int) + d393 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d618, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5373 p hg
    simpa only [d618, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d618, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5390 p hg
    simpa only [d618, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5392 (p : Pattern) (guard : d1134 p = 1) : d619 p ≤ (0 : Int) + d394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d619, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5367 p hg
    simpa only [d619, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d619, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5375 p hg
    simpa only [d619, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5393 (p : Pattern) (guard : d1134 p = 1) : d620 p ≤ (0 : Int) + d395 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d620, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5372 p hg
    simpa only [d620, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d620, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5383 p hg
    simpa only [d620, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5394 (p : Pattern) (guard : d1134 p = 1) : d621 p ≤ (0 : Int) + d396 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d621, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5392 p hg
    simpa only [d621, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d621, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5393 p hg
    simpa only [d621, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5395 (p : Pattern) (guard : d1134 p = 1) : d622 p ≤ (0 : Int) + d397 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d622, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5380 p hg
    simpa only [d622, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d622, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5375 p hg
    simpa only [d622, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5396 (p : Pattern) (guard : d1134 p = 1) : d623 p ≤ (0 : Int) + d398 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d623, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5388 p hg
    simpa only [d623, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d623, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5383 p hg
    simpa only [d623, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5397 (p : Pattern) (guard : d1134 p = 1) : d624 p ≤ (0 : Int) + d399 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d624, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5395 p hg
    simpa only [d624, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d624, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5396 p hg
    simpa only [d624, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5398 (p : Pattern) (guard : d1134 p = 1) : d625 p ≤ (0 : Int) + d400 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d625, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5394 p hg
    simpa only [d625, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d625, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5397 p hg
    simpa only [d625, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5399 (p : Pattern) (guard : d1134 p = 1) : d626 p ≤ (0 : Int) + d401 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d626, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5391 p hg
    simpa only [d626, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d626, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5398 p hg
    simpa only [d626, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5400 (p : Pattern) (guard : d1134 p = 1) : d627 p ≤ (0 : Int) + d402 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d627, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5375 p hg
    simpa only [d627, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d627, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5383 p hg
    simpa only [d627, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5401 (p : Pattern) (guard : d1134 p = 1) : d628 p ≤ (0 : Int) + d403 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d628, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5398 p hg
    simpa only [d628, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d628, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5400 p hg
    simpa only [d628, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5402 (p : Pattern) (guard : d1134 p = 1) : d629 p ≤ (0 : Int) + d404 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d629, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5399 p hg
    simpa only [d629, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d629, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5401 p hg
    simpa only [d629, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5403 (p : Pattern) (guard : d0 p = 1) : d631 p ≤ (0 : Int) + d290 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5404 (p : Pattern) (guard : d1134 p = 1) : d632 p ≤ (0 : Int) + d405 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d632, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5019 p hg
    simpa only [d1134, d632, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d632, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5403 p hg
    simpa only [d1134, d632, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5405 (p : Pattern) (guard : d1134 p = 1) : d633 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d633, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5378 p hg
    simpa only [d633, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d633, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5404 p hg
    simpa only [d633, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5406 (p : Pattern) (guard : d1134 p = 1) : d634 p ≤ (0 : Int) + d407 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d634, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5367 p hg
    simpa only [d634, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d634, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5405 p hg
    simpa only [d634, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5407 (p : Pattern) (guard : d1134 p = 1) : d635 p ≤ (0 : Int) + d408 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d635, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5367 p hg
    simpa only [d635, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d635, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5406 p hg
    simpa only [d635, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5408 (p : Pattern) (guard : d0 p = 1) : d636 p ≤ (0 : Int) + d291 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5409 (p : Pattern) (guard : d1134 p = 1) : d637 p ≤ (0 : Int) + d409 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d637, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5020 p hg
    simpa only [d1134, d637, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d637, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5408 p hg
    simpa only [d1134, d637, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5410 (p : Pattern) (guard : d1134 p = 1) : d638 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d638, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5386 p hg
    simpa only [d638, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d638, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5409 p hg
    simpa only [d638, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5411 (p : Pattern) (guard : d1134 p = 1) : d639 p ≤ (0 : Int) + d411 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d639, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5372 p hg
    simpa only [d639, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d639, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5410 p hg
    simpa only [d639, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5412 (p : Pattern) (guard : d1134 p = 1) : d640 p ≤ (0 : Int) + d412 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d640, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5372 p hg
    simpa only [d640, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d640, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5411 p hg
    simpa only [d640, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5413 (p : Pattern) (guard : d1134 p = 1) : d641 p ≤ (0 : Int) + d413 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d641, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5407 p hg
    simpa only [d641, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d641, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5412 p hg
    simpa only [d641, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5414 (p : Pattern) (guard : d1134 p = 1) : d642 p ≤ (0 : Int) + d414 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d642, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5413 p hg
    simpa only [d642, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d642, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5400 p hg
    simpa only [d642, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5415 (p : Pattern) (guard : d1134 p = 1) : d643 p ≤ (0 : Int) + d415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d643, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5364 p hg
    simpa only [d643, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d643, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5404 p hg
    simpa only [d643, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5416 (p : Pattern) (guard : d1134 p = 1) : d644 p ≤ (0 : Int) + d416 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d644, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5415 p hg
    simpa only [d644, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d644, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5405 p hg
    simpa only [d644, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5417 (p : Pattern) (guard : d1134 p = 1) : d645 p ≤ (0 : Int) + d417 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d645, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5416 p hg
    simpa only [d645, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d645, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5375 p hg
    simpa only [d645, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5418 (p : Pattern) (guard : d1134 p = 1) : d646 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d646, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5369 p hg
    simpa only [d646, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d646, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5409 p hg
    simpa only [d646, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5419 (p : Pattern) (guard : d1134 p = 1) : d647 p ≤ (0 : Int) + d419 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d647, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5418 p hg
    simpa only [d647, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d647, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5410 p hg
    simpa only [d647, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5420 (p : Pattern) (guard : d1134 p = 1) : d648 p ≤ (0 : Int) + d420 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d648, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5419 p hg
    simpa only [d648, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d648, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5383 p hg
    simpa only [d648, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5421 (p : Pattern) (guard : d1134 p = 1) : d649 p ≤ (0 : Int) + d421 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d649, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5417 p hg
    simpa only [d649, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d649, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5420 p hg
    simpa only [d649, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5422 (p : Pattern) (guard : d1134 p = 1) : d650 p ≤ (0 : Int) + d422 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d650, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5421 p hg
    simpa only [d650, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d650, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5400 p hg
    simpa only [d650, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5423 (p : Pattern) (guard : d1134 p = 1) : d651 p ≤ (0 : Int) + d423 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d651, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5414 p hg
    simpa only [d651, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d651, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5422 p hg
    simpa only [d651, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5424 (p : Pattern) (guard : d1134 p = 1) : d652 p ≤ (0 : Int) + d424 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d652, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5406 p hg
    simpa only [d652, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d652, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5375 p hg
    simpa only [d652, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5425 (p : Pattern) (guard : d1134 p = 1) : d653 p ≤ (0 : Int) + d425 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d653, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5411 p hg
    simpa only [d653, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d653, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5383 p hg
    simpa only [d653, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5426 (p : Pattern) (guard : d1134 p = 1) : d654 p ≤ (0 : Int) + d426 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d654, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5424 p hg
    simpa only [d654, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d654, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5425 p hg
    simpa only [d654, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5427 (p : Pattern) (guard : d1134 p = 1) : d655 p ≤ (0 : Int) + d427 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d655, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5426 p hg
    simpa only [d655, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d655, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5400 p hg
    simpa only [d655, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5428 (p : Pattern) (guard : d1134 p = 1) : d656 p ≤ (0 : Int) + d428 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d656, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5427 p hg
    simpa only [d656, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d656, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5400 p hg
    simpa only [d656, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5429 (p : Pattern) (guard : d1134 p = 1) : d657 p ≤ (0 : Int) + d429 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d657, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5423 p hg
    simpa only [d657, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d657, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5428 p hg
    simpa only [d657, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5430 (p : Pattern) (guard : d1134 p = 1) : d658 p ≤ (0 : Int) + d430 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d658, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5402 p hg
    simpa only [d658, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d658, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5429 p hg
    simpa only [d658, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5431 (p : Pattern) (guard : d1 p = 1) : d258 p ≤ (1 : Int) + d258 p := by
  omega
theorem compare5432 (p : Pattern) (guard : d916 p = 1) : d0 p ≤ (0 : Int) + d0 p := by
  omega
theorem compare5433 (p : Pattern) (guard : d1176 p = 1) : d7 p ≤ (0 : Int) + d0 p := by
  cases selected : p 192 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d1176, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5432 p hg
    simpa only [d1176, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1176, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5277 p hg
    simpa only [d1176, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5434 (p : Pattern) (guard : d916 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare5435 (p : Pattern) (guard : d1176 p = 1) : d55 p ≤ (0 : Int) + d2 p := by
  cases selected : p 192 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d1176, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5434 p hg
    simpa only [d1176, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1176, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5284 p hg
    simpa only [d1176, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5436 (p : Pattern) (guard : d1176 p = 1) : d56 p ≤ (0 : Int) + d45 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5433 p hg
    simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5435 p hg
    simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5437 (p : Pattern) (guard : d1176 p = 1) : d57 p ≤ (0 : Int) + d46 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5433 p hg
    simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5436 p hg
    simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5438 (p : Pattern) (guard : d916 p = 1) : d8 p ≤ (0 : Int) + d8 p := by
  omega
theorem compare5439 (p : Pattern) (guard : d0 p = 1) : d10 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5440 (p : Pattern) (guard : d1176 p = 1) : d11 p ≤ (0 : Int) + d8 p := by
  cases selected : p 192 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d1176, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5438 p hg
    simpa only [d1176, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1176, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5439 p hg
    simpa only [d1176, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5441 (p : Pattern) (guard : d1176 p = 1) : d12 p ≤ (0 : Int) + d1055 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5433 p hg
    simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5440 p hg
    simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5442 (p : Pattern) (guard : d916 p = 1) : d9 p ≤ (0 : Int) + d9 p := by
  omega
theorem compare5443 (p : Pattern) (guard : d0 p = 1) : d59 p ≤ (0 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5444 (p : Pattern) (guard : d1176 p = 1) : d60 p ≤ (0 : Int) + d9 p := by
  cases selected : p 192 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d1176, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5442 p hg
    simpa only [d1176, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1176, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5443 p hg
    simpa only [d1176, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5445 (p : Pattern) (guard : d1176 p = 1) : d61 p ≤ (0 : Int) + d1056 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5440 p hg
    simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5444 p hg
    simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5446 (p : Pattern) (guard : d1176 p = 1) : d62 p ≤ (0 : Int) + d1057 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5436 p hg
    simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5445 p hg
    simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5447 (p : Pattern) (guard : d1176 p = 1) : d63 p ≤ (0 : Int) + d1058 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5441 p hg
    simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5446 p hg
    simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5448 (p : Pattern) (guard : d1176 p = 1) : d64 p ≤ (0 : Int) + d1059 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5437 p hg
    simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5447 p hg
    simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5449 (p : Pattern) (guard : d1176 p = 1) : d106 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5433 p hg
    simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5435 p hg
    simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5450 (p : Pattern) (guard : d1176 p = 1) : d119 p ≤ (0 : Int) + d82 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5433 p hg
    simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5435 p hg
    simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5451 (p : Pattern) (guard : d1176 p = 1) : d120 p ≤ (0 : Int) + d83 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5433 p hg
    simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5450 p hg
    simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5452 (p : Pattern) (guard : d1176 p = 1) : d121 p ≤ (0 : Int) + d84 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5451 p hg
    simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5435 p hg
    simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5453 (p : Pattern) (guard : d1176 p = 1) : d122 p ≤ (0 : Int) + d85 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5449 p hg
    simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5452 p hg
    simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5454 (p : Pattern) (guard : d1176 p = 1) : d179 p ≤ (0 : Int) + d162 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5449 p hg
    simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5453 p hg
    simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5455 (p : Pattern) (guard : d1176 p = 1) : d65 p ≤ (0 : Int) + d1060 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5435 p hg
    simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5444 p hg
    simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5456 (p : Pattern) (guard : d1176 p = 1) : d109 p ≤ (0 : Int) + d1061 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5441 p hg
    simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5455 p hg
    simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5457 (p : Pattern) (guard : d1176 p = 1) : d125 p ≤ (0 : Int) + d1062 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5440 p hg
    simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5444 p hg
    simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5458 (p : Pattern) (guard : d1176 p = 1) : d126 p ≤ (0 : Int) + d1063 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5440 p hg
    simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5457 p hg
    simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5459 (p : Pattern) (guard : d1176 p = 1) : d127 p ≤ (0 : Int) + d1064 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5451 p hg
    simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5458 p hg
    simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
