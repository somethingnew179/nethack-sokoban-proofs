/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons038
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5460 (p : Pattern) (guard : d1176 p = 1) : d128 p ≤ (0 : Int) + d1065 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5459 p hg
    simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5455 p hg
    simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5461 (p : Pattern) (guard : d1176 p = 1) : d129 p ≤ (0 : Int) + d1066 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5456 p hg
    simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5460 p hg
    simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5462 (p : Pattern) (guard : d1176 p = 1) : d237 p ≤ (0 : Int) + d1067 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5456 p hg
    simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5461 p hg
    simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5463 (p : Pattern) (guard : d1176 p = 1) : d238 p ≤ (0 : Int) + d1068 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5454 p hg
    simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5462 p hg
    simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5464 (p : Pattern) (guard : d1176 p = 1) : d239 p ≤ (0 : Int) + d1069 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5448 p hg
    simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5463 p hg
    simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5465 (p : Pattern) (guard : d1176 p = 1) : d68 p ≤ (0 : Int) + d48 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5437 p hg
    simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5435 p hg
    simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5466 (p : Pattern) (guard : d1176 p = 1) : d69 p ≤ (0 : Int) + d1070 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5447 p hg
    simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5455 p hg
    simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5467 (p : Pattern) (guard : d1176 p = 1) : d70 p ≤ (0 : Int) + d1071 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5465 p hg
    simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5466 p hg
    simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5468 (p : Pattern) (guard : d1176 p = 1) : d181 p ≤ (0 : Int) + d164 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5453 p hg
    simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5435 p hg
    simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5469 (p : Pattern) (guard : d1176 p = 1) : d240 p ≤ (0 : Int) + d1072 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5461 p hg
    simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5455 p hg
    simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5470 (p : Pattern) (guard : d1176 p = 1) : d241 p ≤ (0 : Int) + d1073 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5468 p hg
    simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5469 p hg
    simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5471 (p : Pattern) (guard : d1176 p = 1) : d242 p ≤ (0 : Int) + d1074 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5467 p hg
    simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5470 p hg
    simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5472 (p : Pattern) (guard : d1176 p = 1) : d243 p ≤ (0 : Int) + d1075 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5464 p hg
    simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5471 p hg
    simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5473 (p : Pattern) (guard : d1176 p = 1) : d66 p ≤ (0 : Int) + d1076 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5435 p hg
    simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5455 p hg
    simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5474 (p : Pattern) (guard : d1176 p = 1) : d244 p ≤ (0 : Int) + d1077 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5471 p hg
    simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5473 p hg
    simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5475 (p : Pattern) (guard : d1176 p = 1) : d245 p ≤ (0 : Int) + d1078 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5472 p hg
    simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5474 p hg
    simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5476 (p : Pattern) (guard : d1176 p = 1) : d137 p ≤ (0 : Int) + d92 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5450 p hg
    simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5435 p hg
    simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5477 (p : Pattern) (guard : d1176 p = 1) : d139 p ≤ (0 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5451 p hg
    simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5476 p hg
    simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5478 (p : Pattern) (guard : d1176 p = 1) : d153 p ≤ (0 : Int) + d100 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5437 p hg
    simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5477 p hg
    simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5479 (p : Pattern) (guard : d1176 p = 1) : d186 p ≤ (0 : Int) + d169 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5437 p hg
    simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5478 p hg
    simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5480 (p : Pattern) (guard : d1176 p = 1) : d143 p ≤ (0 : Int) + d1079 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5457 p hg
    simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5444 p hg
    simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5481 (p : Pattern) (guard : d1176 p = 1) : d144 p ≤ (0 : Int) + d1080 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5476 p hg
    simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5480 p hg
    simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5482 (p : Pattern) (guard : d1176 p = 1) : d146 p ≤ (0 : Int) + d1081 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5459 p hg
    simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5481 p hg
    simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5483 (p : Pattern) (guard : d1176 p = 1) : d155 p ≤ (0 : Int) + d1082 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5447 p hg
    simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5482 p hg
    simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5484 (p : Pattern) (guard : d1176 p = 1) : d246 p ≤ (0 : Int) + d1083 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5447 p hg
    simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5483 p hg
    simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5485 (p : Pattern) (guard : d1176 p = 1) : d247 p ≤ (0 : Int) + d1084 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5479 p hg
    simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5484 p hg
    simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5486 (p : Pattern) (guard : d1176 p = 1) : d248 p ≤ (0 : Int) + d1085 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5485 p hg
    simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5473 p hg
    simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5487 (p : Pattern) (guard : d1176 p = 1) : d138 p ≤ (0 : Int) + d93 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5433 p hg
    simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5476 p hg
    simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5488 (p : Pattern) (guard : d1176 p = 1) : d140 p ≤ (0 : Int) + d95 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5487 p hg
    simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5477 p hg
    simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5489 (p : Pattern) (guard : d1176 p = 1) : d188 p ≤ (0 : Int) + d171 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5488 p hg
    simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5435 p hg
    simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5490 (p : Pattern) (guard : d1176 p = 1) : d145 p ≤ (0 : Int) + d1086 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5441 p hg
    simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5481 p hg
    simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5491 (p : Pattern) (guard : d1176 p = 1) : d147 p ≤ (0 : Int) + d1087 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5490 p hg
    simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5482 p hg
    simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5492 (p : Pattern) (guard : d1176 p = 1) : d249 p ≤ (0 : Int) + d1088 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5491 p hg
    simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5455 p hg
    simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5493 (p : Pattern) (guard : d1176 p = 1) : d250 p ≤ (0 : Int) + d1089 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5489 p hg
    simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5492 p hg
    simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5494 (p : Pattern) (guard : d1176 p = 1) : d251 p ≤ (0 : Int) + d1090 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5493 p hg
    simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5473 p hg
    simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5495 (p : Pattern) (guard : d1176 p = 1) : d252 p ≤ (0 : Int) + d1091 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5486 p hg
    simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5494 p hg
    simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5496 (p : Pattern) (guard : d1176 p = 1) : d191 p ≤ (0 : Int) + d174 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5478 p hg
    simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5435 p hg
    simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5497 (p : Pattern) (guard : d1176 p = 1) : d253 p ≤ (0 : Int) + d1092 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5483 p hg
    simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5455 p hg
    simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5498 (p : Pattern) (guard : d1176 p = 1) : d254 p ≤ (0 : Int) + d1093 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5496 p hg
    simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5497 p hg
    simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5499 (p : Pattern) (guard : d1176 p = 1) : d255 p ≤ (0 : Int) + d1094 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5498 p hg
    simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5473 p hg
    simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5500 (p : Pattern) (guard : d1176 p = 1) : d256 p ≤ (0 : Int) + d1095 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5499 p hg
    simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5473 p hg
    simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5501 (p : Pattern) (guard : d1176 p = 1) : d257 p ≤ (0 : Int) + d1096 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5495 p hg
    simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5500 p hg
    simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5502 (p : Pattern) (guard : d1176 p = 1) : d258 p ≤ (0 : Int) + d1097 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5475 p hg
    simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5501 p hg
    simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5503 (p : Pattern) (guard : d770 p = 1) : d64 p ≤ (0 : Int) + d57 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3415 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3053 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5504 (p : Pattern) (guard : d770 p = 1) : d238 p ≤ (0 : Int) + d179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3417 p hg
    simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3062 p hg
    simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5505 (p : Pattern) (guard : d770 p = 1) : d239 p ≤ (0 : Int) + d180 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5503 p hg
    simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5504 p hg
    simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5506 (p : Pattern) (guard : d770 p = 1) : d70 p ≤ (0 : Int) + d68 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3420 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3065 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5507 (p : Pattern) (guard : d770 p = 1) : d241 p ≤ (0 : Int) + d181 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3422 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3067 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5508 (p : Pattern) (guard : d770 p = 1) : d242 p ≤ (0 : Int) + d182 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5506 p hg
    simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5507 p hg
    simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5509 (p : Pattern) (guard : d770 p = 1) : d243 p ≤ (0 : Int) + d183 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5505 p hg
    simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5508 p hg
    simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5510 (p : Pattern) (guard : d770 p = 1) : d66 p ≤ (0 : Int) + d55 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3426 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3056 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5511 (p : Pattern) (guard : d770 p = 1) : d244 p ≤ (0 : Int) + d184 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5508 p hg
    simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5510 p hg
    simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5512 (p : Pattern) (guard : d770 p = 1) : d245 p ≤ (0 : Int) + d185 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5509 p hg
    simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5511 p hg
    simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5513 (p : Pattern) (guard : d770 p = 1) : d247 p ≤ (0 : Int) + d186 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3430 p hg
    simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3078 p hg
    simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5514 (p : Pattern) (guard : d770 p = 1) : d248 p ≤ (0 : Int) + d187 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5513 p hg
    simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5510 p hg
    simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5515 (p : Pattern) (guard : d770 p = 1) : d250 p ≤ (0 : Int) + d188 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3433 p hg
    simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3083 p hg
    simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5516 (p : Pattern) (guard : d770 p = 1) : d251 p ≤ (0 : Int) + d189 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5515 p hg
    simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5510 p hg
    simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5517 (p : Pattern) (guard : d770 p = 1) : d252 p ≤ (0 : Int) + d190 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5514 p hg
    simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5516 p hg
    simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5518 (p : Pattern) (guard : d770 p = 1) : d254 p ≤ (0 : Int) + d191 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3437 p hg
    simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3087 p hg
    simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5519 (p : Pattern) (guard : d770 p = 1) : d255 p ≤ (0 : Int) + d192 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5518 p hg
    simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5510 p hg
    simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5520 (p : Pattern) (guard : d770 p = 1) : d256 p ≤ (0 : Int) + d193 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5519 p hg
    simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5510 p hg
    simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5521 (p : Pattern) (guard : d770 p = 1) : d257 p ≤ (0 : Int) + d194 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5517 p hg
    simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5520 p hg
    simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5522 (p : Pattern) (guard : d770 p = 1) : d258 p ≤ (0 : Int) + d195 p := by
  cases selected : p 108 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5512 p hg
    simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5521 p hg
    simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5523 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (0 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare287 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5524 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (0 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5523 p hg
    simpa only [d106, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d106, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5525 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (0 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare324 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5524 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5526 (p : Pattern) (guard : d0 p = 1) : d122 p ≤ (0 : Int) + d122 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5527 (p : Pattern) (guard : d742 p = 1) : d179 p ≤ (0 : Int) + d122 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5525 p hg
    simpa only [d742, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5526 p hg
    simpa only [d742, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5528 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (0 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare302 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5529 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (0 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d12, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5523 p hg
    simpa only [d12, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d12, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5528 p hg
    simpa only [d12, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5530 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (0 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5529 p hg
    simpa only [d109, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare440 p hg
    simpa only [d109, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5531 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (0 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare327 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5530 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5532 (p : Pattern) (guard : d0 p = 1) : d129 p ≤ (0 : Int) + d129 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5533 (p : Pattern) (guard : d742 p = 1) : d237 p ≤ (0 : Int) + d129 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5531 p hg
    simpa only [d742, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5532 p hg
    simpa only [d742, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5534 (p : Pattern) (guard : d742 p = 1) : d238 p ≤ (0 : Int) + d775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d238, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5527 p hg
    simpa only [d238, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d238, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5533 p hg
    simpa only [d238, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5535 (p : Pattern) (guard : d742 p = 1) : d239 p ≤ (0 : Int) + d776 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d239, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1444 p hg
    simpa only [d239, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d239, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5534 p hg
    simpa only [d239, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5536 (p : Pattern) (guard : d742 p = 1) : d68 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3596 p hg
    simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5537 (p : Pattern) (guard : d742 p = 1) : d69 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3600 p hg
    simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5538 (p : Pattern) (guard : d742 p = 1) : d70 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5536 p hg
    simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5537 p hg
    simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5539 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (0 : Int) + d55 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5540 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (0 : Int) + d55 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5539 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3605 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5541 (p : Pattern) (guard : d742 p = 1) : d181 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5540 p hg
    simpa only [d742, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d742, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5542 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (0 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare457 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare440 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5543 (p : Pattern) (guard : d1 p = 1) : d129 p ≤ (0 : Int) + d65 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5542 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3609 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5544 (p : Pattern) (guard : d742 p = 1) : d240 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5543 p hg
    simpa only [d742, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d742, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5545 (p : Pattern) (guard : d742 p = 1) : d241 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5541 p hg
    simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5544 p hg
    simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5546 (p : Pattern) (guard : d742 p = 1) : d242 p ≤ (0 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5538 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5545 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5547 (p : Pattern) (guard : d742 p = 1) : d243 p ≤ (0 : Int) + d778 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d243, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5535 p hg
    simpa only [d243, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d243, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5546 p hg
    simpa only [d243, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5548 (p : Pattern) (guard : d742 p = 1) : d244 p ≤ (0 : Int) + d66 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5546 p hg
    simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5549 (p : Pattern) (guard : d742 p = 1) : d245 p ≤ (0 : Int) + d1189 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d245, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5547 p hg
    simpa only [d245, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d245, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5548 p hg
    simpa only [d245, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5550 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (0 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5523 p hg
    simpa only [d57, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare288 p hg
    simpa only [d57, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5551 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (0 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5550 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5552 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5553 (p : Pattern) (guard : d742 p = 1) : d186 p ≤ (0 : Int) + d153 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5551 p hg
    simpa only [d742, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5552 p hg
    simpa only [d742, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5554 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5529 p hg
    simpa only [d63, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare305 p hg
    simpa only [d63, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5555 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (0 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5554 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5556 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5557 (p : Pattern) (guard : d742 p = 1) : d246 p ≤ (0 : Int) + d155 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5555 p hg
    simpa only [d742, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5556 p hg
    simpa only [d742, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5558 (p : Pattern) (guard : d742 p = 1) : d247 p ≤ (0 : Int) + d783 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d247, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5553 p hg
    simpa only [d247, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d247, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5557 p hg
    simpa only [d247, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5559 (p : Pattern) (guard : d742 p = 1) : d248 p ≤ (0 : Int) + d784 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d248, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5558 p hg
    simpa only [d248, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d248, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d248, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5560 (p : Pattern) (guard : d742 p = 1) : d188 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare454 p hg
    simpa only [d742, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d742, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5561 (p : Pattern) (guard : d742 p = 1) : d249 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare465 p hg
    simpa only [d742, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d742, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5562 (p : Pattern) (guard : d742 p = 1) : d250 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d250, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5560 p hg
    simpa only [d250, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d250, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5561 p hg
    simpa only [d250, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5563 (p : Pattern) (guard : d742 p = 1) : d251 p ≤ (0 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5562 p hg
    simpa only [d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5564 (p : Pattern) (guard : d742 p = 1) : d252 p ≤ (0 : Int) + d785 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d252, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5559 p hg
    simpa only [d252, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d252, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5563 p hg
    simpa only [d252, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5565 (p : Pattern) (guard : d1 p = 1) : d153 p ≤ (0 : Int) + d55 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3596 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare453 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5566 (p : Pattern) (guard : d742 p = 1) : d191 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5565 p hg
    simpa only [d742, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d742, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5567 (p : Pattern) (guard : d1 p = 1) : d155 p ≤ (0 : Int) + d65 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3600 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare464 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5568 (p : Pattern) (guard : d742 p = 1) : d253 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5567 p hg
    simpa only [d742, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d742, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5569 (p : Pattern) (guard : d742 p = 1) : d254 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d254, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5566 p hg
    simpa only [d254, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d254, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5568 p hg
    simpa only [d254, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5570 (p : Pattern) (guard : d742 p = 1) : d255 p ≤ (0 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5569 p hg
    simpa only [d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5571 (p : Pattern) (guard : d742 p = 1) : d256 p ≤ (0 : Int) + d66 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5570 p hg
    simpa only [d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5572 (p : Pattern) (guard : d742 p = 1) : d257 p ≤ (0 : Int) + d1190 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d257, d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5564 p hg
    simpa only [d257, d1190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d257, d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5571 p hg
    simpa only [d257, d1190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5573 (p : Pattern) (guard : d742 p = 1) : d258 p ≤ (0 : Int) + d1191 p := by
  cases selected : p 108 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d258, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5549 p hg
    simpa only [d258, d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d258, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5572 p hg
    simpa only [d258, d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5574 (p : Pattern) (guard : d794 p = 1) : d64 p ≤ (0 : Int) + d64 p := by
  omega
theorem compare5575 (p : Pattern) (guard : d794 p = 1) : d106 p ≤ (0 : Int) + d106 p := by
  omega
theorem compare5576 (p : Pattern) (guard : d0 p = 1) : d121 p ≤ (0 : Int) + d121 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5577 (p : Pattern) (guard : d794 p = 1) : d122 p ≤ (0 : Int) + d121 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5524 p hg
    simpa only [d794, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5576 p hg
    simpa only [d794, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5578 (p : Pattern) (guard : d794 p = 1) : d179 p ≤ (0 : Int) + d1192 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d179, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5575 p hg
    simpa only [d179, d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d179, d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5577 p hg
    simpa only [d179, d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5579 (p : Pattern) (guard : d794 p = 1) : d109 p ≤ (0 : Int) + d109 p := by
  omega
theorem compare5580 (p : Pattern) (guard : d0 p = 1) : d128 p ≤ (0 : Int) + d128 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5581 (p : Pattern) (guard : d794 p = 1) : d129 p ≤ (0 : Int) + d128 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5530 p hg
    simpa only [d794, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5580 p hg
    simpa only [d794, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5582 (p : Pattern) (guard : d794 p = 1) : d237 p ≤ (0 : Int) + d1193 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d237, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5579 p hg
    simpa only [d237, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d237, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5581 p hg
    simpa only [d237, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5583 (p : Pattern) (guard : d794 p = 1) : d238 p ≤ (0 : Int) + d1194 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d238, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5578 p hg
    simpa only [d238, d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d238, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5582 p hg
    simpa only [d238, d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5584 (p : Pattern) (guard : d794 p = 1) : d239 p ≤ (0 : Int) + d1195 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d239, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5574 p hg
    simpa only [d239, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d239, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5583 p hg
    simpa only [d239, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5585 (p : Pattern) (guard : d794 p = 1) : d70 p ≤ (0 : Int) + d70 p := by
  omega
theorem compare5586 (p : Pattern) (guard : d794 p = 1) : d181 p ≤ (0 : Int) + d1196 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d181, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5577 p hg
    simpa only [d181, d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d181, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare519 p hg
    simpa only [d181, d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5587 (p : Pattern) (guard : d794 p = 1) : d240 p ≤ (0 : Int) + d1197 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d240, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5581 p hg
    simpa only [d240, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d240, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare521 p hg
    simpa only [d240, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5588 (p : Pattern) (guard : d794 p = 1) : d241 p ≤ (0 : Int) + d1198 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d241, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5586 p hg
    simpa only [d241, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d241, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5587 p hg
    simpa only [d241, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5589 (p : Pattern) (guard : d794 p = 1) : d242 p ≤ (0 : Int) + d1199 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d242, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5585 p hg
    simpa only [d242, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d242, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5588 p hg
    simpa only [d242, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5590 (p : Pattern) (guard : d794 p = 1) : d243 p ≤ (0 : Int) + d1200 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d243, d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5584 p hg
    simpa only [d243, d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d243, d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5589 p hg
    simpa only [d243, d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5591 (p : Pattern) (guard : d794 p = 1) : d244 p ≤ (0 : Int) + d1201 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d244, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5589 p hg
    simpa only [d244, d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d244, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d244, d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5592 (p : Pattern) (guard : d794 p = 1) : d245 p ≤ (0 : Int) + d1202 p := by
  cases selected : p 132 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d245, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5590 p hg
    simpa only [d245, d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d245, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5591 p hg
    simpa only [d245, d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5593 (p : Pattern) (guard : d794 p = 1) : d57 p ≤ (0 : Int) + d57 p := by
  omega
theorem compare5594 (p : Pattern) (guard : d0 p = 1) : d139 p ≤ (0 : Int) + d139 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5595 (p : Pattern) (guard : d794 p = 1) : d153 p ≤ (0 : Int) + d139 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5550 p hg
    simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5594 p hg
    simpa only [d794, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5596 (p : Pattern) (guard : d794 p = 1) : d186 p ≤ (0 : Int) + d1203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d186, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5593 p hg
    simpa only [d186, d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d186, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5595 p hg
    simpa only [d186, d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5597 (p : Pattern) (guard : d794 p = 1) : d63 p ≤ (0 : Int) + d63 p := by
  omega
theorem compare5598 (p : Pattern) (guard : d0 p = 1) : d146 p ≤ (0 : Int) + d146 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5599 (p : Pattern) (guard : d794 p = 1) : d155 p ≤ (0 : Int) + d146 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5554 p hg
    simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5598 p hg
    simpa only [d794, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
