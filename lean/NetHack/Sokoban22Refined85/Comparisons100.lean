/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons099
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare14000 (p : Pattern) (guard : d4395 p = 1) : d1489 p ≤ (0 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1489, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d1489, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1489, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13999 p hg
    simpa only [d4395, d1489, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14001 (p : Pattern) (guard : d0 p = 1) : d1490 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14002 (p : Pattern) (guard : d4670 p = 1) : d1491 p ≤ (0 : Int) + d930 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1491, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14000 p hg
    simpa only [d4670, d1491, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1491, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14001 p hg
    simpa only [d4670, d1491, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14003 (p : Pattern) (guard : d4670 p = 1) : d1492 p ≤ (0 : Int) + d932 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1492, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14002 p hg
    simpa only [d1492, d932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1492, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8890 p hg
    simpa only [d1492, d932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14004 (p : Pattern) (guard : d0 p = 1) : d1385 p ≤ (0 : Int) + d211 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14005 (p : Pattern) (guard : d4395 p = 1) : d1493 p ≤ (0 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1493, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4395, d1493, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1493, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14004 p hg
    simpa only [d4395, d1493, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14006 (p : Pattern) (guard : d4670 p = 1) : d1494 p ≤ (0 : Int) + d931 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1494, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14005 p hg
    simpa only [d4670, d1494, d931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1494, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8892 p hg
    simpa only [d4670, d1494, d931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14007 (p : Pattern) (guard : d4670 p = 1) : d1495 p ≤ (0 : Int) + d935 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1495, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14006 p hg
    simpa only [d1495, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1495, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8895 p hg
    simpa only [d1495, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14008 (p : Pattern) (guard : d4670 p = 1) : d1496 p ≤ (0 : Int) + d936 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1496, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14003 p hg
    simpa only [d1496, d936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1496, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14007 p hg
    simpa only [d1496, d936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14009 (p : Pattern) (guard : d4670 p = 1) : d1497 p ≤ (0 : Int) + d937 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1497, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13998 p hg
    simpa only [d1497, d937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1497, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14008 p hg
    simpa only [d1497, d937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14010 (p : Pattern) (guard : d0 p = 1) : d293 p ≤ (0 : Int) + d252 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14011 (p : Pattern) (guard : d4395 p = 1) : d1489 p ≤ (0 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1489, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d1489, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1489, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14010 p hg
    simpa only [d4395, d1489, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14012 (p : Pattern) (guard : d4670 p = 1) : d1491 p ≤ (0 : Int) + d938 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1491, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14011 p hg
    simpa only [d4670, d1491, d938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1491, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14001 p hg
    simpa only [d4670, d1491, d938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14013 (p : Pattern) (guard : d4670 p = 1) : d1492 p ≤ (0 : Int) + d941 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1492, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14012 p hg
    simpa only [d1492, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1492, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8904 p hg
    simpa only [d1492, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14014 (p : Pattern) (guard : d4670 p = 1) : d1496 p ≤ (0 : Int) + d942 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1496, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14013 p hg
    simpa only [d1496, d942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1496, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14007 p hg
    simpa only [d1496, d942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14015 (p : Pattern) (guard : d4670 p = 1) : d1498 p ≤ (0 : Int) + d943 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1498, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14014 p hg
    simpa only [d1498, d943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1498, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d1498, d943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14016 (p : Pattern) (guard : d4670 p = 1) : d1499 p ≤ (0 : Int) + d944 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1499, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14009 p hg
    simpa only [d1499, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1499, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14015 p hg
    simpa only [d1499, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14017 (p : Pattern) (guard : d4670 p = 1) : d1500 p ≤ (0 : Int) + d945 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1500, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13985 p hg
    simpa only [d1500, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1500, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14016 p hg
    simpa only [d1500, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14018 (p : Pattern) (guard : d4670 p = 1) : d1501 p ≤ (0 : Int) + d946 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1501, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13884 p hg
    simpa only [d1501, d946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1501, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14017 p hg
    simpa only [d1501, d946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14019 (p : Pattern) (guard : d4670 p = 1) : d1502 p ≤ (0 : Int) + d947 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1502, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13973 p hg
    simpa only [d1502, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1502, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14018 p hg
    simpa only [d1502, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14020 (p : Pattern) (guard : d4670 p = 1) : d1503 p ≤ (0 : Int) + d948 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1503, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13956 p hg
    simpa only [d1503, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1503, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14019 p hg
    simpa only [d1503, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14021 (p : Pattern) (guard : d4147 p = 1) : d16 p ≤ (2 : Int) + d16 p := by
  omega
theorem compare14022 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14023 (p : Pattern) (guard : d4147 p = 1) : d21 p ≤ (2 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14022 p hg
    simpa only [d4147, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4869 p hg
    simpa only [d4147, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14024 (p : Pattern) (guard : d4147 p = 1) : d22 p ≤ (2 : Int) + d4311 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d22, d4311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14021 p hg
    simpa only [d22, d4311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d22, d4311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14023 p hg
    simpa only [d22, d4311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14025 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) ≤ (2 : Int) + 2
  decide
theorem compare14026 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (2 : Int) + d30 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14025 p hg
    simpa only [d13, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d13, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14027 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14025 p hg
    simpa only [d14, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14026 p hg
    simpa only [d14, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14028 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (2 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14027 p hg
    simpa only [d33, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6680 p hg
    simpa only [d33, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14029 (p : Pattern) (guard : d4147 p = 1) : d950 p ≤ (2 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14022 p hg
    simpa only [d4147, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14028 p hg
    simpa only [d4147, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14030 (p : Pattern) (guard : d0 p = 1) : d26 p ≤ (2 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14031 (p : Pattern) (guard : d4147 p = 1) : d27 p ≤ (2 : Int) + d62 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14030 p hg
    simpa only [d4147, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d4147, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14032 (p : Pattern) (guard : d4147 p = 1) : d1399 p ≤ (2 : Int) + d4312 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1399, d4312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14029 p hg
    simpa only [d1399, d4312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1399, d4312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14031 p hg
    simpa only [d1399, d4312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14033 (p : Pattern) (guard : d4147 p = 1) : d1400 p ≤ (2 : Int) + d4313 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1400, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14024 p hg
    simpa only [d1400, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1400, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14032 p hg
    simpa only [d1400, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14034 (p : Pattern) (guard : d0 p = 1) : d33 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14035 (p : Pattern) (guard : d4147 p = 1) : d33 p ≤ (2 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14034 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14028 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14036 (p : Pattern) (guard : d0 p = 1) : d42 p ≤ (2 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14037 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (2 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4867 p hg
    simpa only [d43, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d43, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14038 (p : Pattern) (guard : d4147 p = 1) : d44 p ≤ (2 : Int) + d66 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14036 p hg
    simpa only [d4147, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14037 p hg
    simpa only [d4147, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14039 (p : Pattern) (guard : d4147 p = 1) : d1401 p ≤ (2 : Int) + d4314 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1401, d4314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14035 p hg
    simpa only [d1401, d4314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1401, d4314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14038 p hg
    simpa only [d1401, d4314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14040 (p : Pattern) (guard : d0 p = 1) : d46 p ≤ (2 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14041 (p : Pattern) (guard : d4147 p = 1) : d47 p ≤ (2 : Int) + d66 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14040 p hg
    simpa only [d4147, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14037 p hg
    simpa only [d4147, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14042 (p : Pattern) (guard : d0 p = 1) : d48 p ≤ (2 : Int) + d72 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14043 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4731 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14044 (p : Pattern) (guard : d4147 p = 1) : d49 p ≤ (2 : Int) + d72 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14042 p hg
    simpa only [d4147, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14043 p hg
    simpa only [d4147, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14045 (p : Pattern) (guard : d4147 p = 1) : d50 p ≤ (2 : Int) + d4315 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d50, d4315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14041 p hg
    simpa only [d50, d4315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d50, d4315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14044 p hg
    simpa only [d50, d4315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14046 (p : Pattern) (guard : d4147 p = 1) : d1402 p ≤ (2 : Int) + d4316 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1402, d4316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14039 p hg
    simpa only [d1402, d4316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1402, d4316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14045 p hg
    simpa only [d1402, d4316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14047 (p : Pattern) (guard : d4147 p = 1) : d1403 p ≤ (2 : Int) + d4317 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1403, d4317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14033 p hg
    simpa only [d1403, d4317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1403, d4317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14046 p hg
    simpa only [d1403, d4317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14048 (p : Pattern) (guard : d0 p = 1) : d1409 p ≤ (2 : Int) + d4317 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14049 (p : Pattern) (guard : d4304 p = 1) : d1410 p ≤ (2 : Int) + d4317 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14047 p hg
    simpa only [d4304, d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14048 p hg
    simpa only [d4304, d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14050 (p : Pattern) (guard : d4147 p = 1) : d54 p ≤ (2 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14022 p hg
    simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6706 p hg
    simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14051 (p : Pattern) (guard : d4147 p = 1) : d1411 p ≤ (2 : Int) + d4312 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1411, d4312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14050 p hg
    simpa only [d1411, d4312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1411, d4312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14031 p hg
    simpa only [d1411, d4312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14052 (p : Pattern) (guard : d4147 p = 1) : d1412 p ≤ (2 : Int) + d4313 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1412, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14024 p hg
    simpa only [d1412, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1412, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14051 p hg
    simpa only [d1412, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14053 (p : Pattern) (guard : d4147 p = 1) : d53 p ≤ (2 : Int) + d53 p := by
  omega
theorem compare14054 (p : Pattern) (guard : d0 p = 1) : d62 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14055 (p : Pattern) (guard : d4147 p = 1) : d63 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14054 p hg
    simpa only [d4147, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d4147, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14056 (p : Pattern) (guard : d4147 p = 1) : d1413 p ≤ (2 : Int) + d968 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1413, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14053 p hg
    simpa only [d1413, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1413, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14055 p hg
    simpa only [d1413, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14057 (p : Pattern) (guard : d4147 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare14058 (p : Pattern) (guard : d4147 p = 1) : d1414 p ≤ (2 : Int) + d969 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1414, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14056 p hg
    simpa only [d1414, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1414, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14057 p hg
    simpa only [d1414, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14059 (p : Pattern) (guard : d4147 p = 1) : d1415 p ≤ (2 : Int) + d4321 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1415, d4321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14052 p hg
    simpa only [d1415, d4321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1415, d4321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14058 p hg
    simpa only [d1415, d4321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14060 (p : Pattern) (guard : d0 p = 1) : d1419 p ≤ (2 : Int) + d4321 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14061 (p : Pattern) (guard : d4304 p = 1) : d1420 p ≤ (2 : Int) + d4321 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14059 p hg
    simpa only [d4304, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14060 p hg
    simpa only [d4304, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14062 (p : Pattern) (guard : d4304 p = 1) : d1421 p ≤ (2 : Int) + d5244 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1421, d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14049 p hg
    simpa only [d1421, d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1421, d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14061 p hg
    simpa only [d1421, d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14063 (p : Pattern) (guard : d4147 p = 1) : d89 p ≤ (2 : Int) + d62 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14030 p hg
    simpa only [d4147, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6164 p hg
    simpa only [d4147, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14064 (p : Pattern) (guard : d4147 p = 1) : d90 p ≤ (2 : Int) + d4160 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d90, d4160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14063 p hg
    simpa only [d90, d4160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d90, d4160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14055 p hg
    simpa only [d90, d4160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14065 (p : Pattern) (guard : d4147 p = 1) : d91 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14055 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14057 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14066 (p : Pattern) (guard : d4147 p = 1) : d92 p ≤ (2 : Int) + d4161 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d92, d4161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14064 p hg
    simpa only [d92, d4161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d92, d4161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14065 p hg
    simpa only [d92, d4161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14067 (p : Pattern) (guard : d4147 p = 1) : d93 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14065 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14057 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14068 (p : Pattern) (guard : d4147 p = 1) : d94 p ≤ (2 : Int) + d4162 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d94, d4162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14066 p hg
    simpa only [d94, d4162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d94, d4162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14067 p hg
    simpa only [d94, d4162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14069 (p : Pattern) (guard : d0 p = 1) : d95 p ≤ (2 : Int) + d4162 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14070 (p : Pattern) (guard : d4304 p = 1) : d96 p ≤ (2 : Int) + d4162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14068 p hg
    simpa only [d4304, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14069 p hg
    simpa only [d4304, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14071 (p : Pattern) (guard : d4304 p = 1) : d1422 p ≤ (2 : Int) + d5245 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1422, d5245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14061 p hg
    simpa only [d1422, d5245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1422, d5245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14070 p hg
    simpa only [d1422, d5245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14072 (p : Pattern) (guard : d4304 p = 1) : d1423 p ≤ (2 : Int) + d5246 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1423, d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14062 p hg
    simpa only [d1423, d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1423, d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14071 p hg
    simpa only [d1423, d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14073 (p : Pattern) (guard : d0 p = 1) : d1425 p ≤ (2 : Int) + d4317 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14074 (p : Pattern) (guard : d4304 p = 1) : d1426 p ≤ (2 : Int) + d4317 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14047 p hg
    simpa only [d4304, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14073 p hg
    simpa only [d4304, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14075 (p : Pattern) (guard : d4304 p = 1) : d1427 p ≤ (2 : Int) + d5244 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1427, d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14074 p hg
    simpa only [d1427, d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1427, d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14061 p hg
    simpa only [d1427, d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14076 (p : Pattern) (guard : d4304 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare14077 (p : Pattern) (guard : d4304 p = 1) : d1428 p ≤ (2 : Int) + d5247 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1428, d5247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14061 p hg
    simpa only [d1428, d5247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1428, d5247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14076 p hg
    simpa only [d1428, d5247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14078 (p : Pattern) (guard : d4304 p = 1) : d1429 p ≤ (2 : Int) + d5248 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1429, d5248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14075 p hg
    simpa only [d1429, d5248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1429, d5248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14077 p hg
    simpa only [d1429, d5248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14079 (p : Pattern) (guard : d4304 p = 1) : d1430 p ≤ (2 : Int) + d5249 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1430, d5249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14072 p hg
    simpa only [d1430, d5249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1430, d5249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14078 p hg
    simpa only [d1430, d5249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14080 (p : Pattern) (guard : d0 p = 1) : d1433 p ≤ (2 : Int) + d4317 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14081 (p : Pattern) (guard : d4304 p = 1) : d1434 p ≤ (2 : Int) + d4317 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14047 p hg
    simpa only [d4304, d1434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14080 p hg
    simpa only [d4304, d1434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14082 (p : Pattern) (guard : d4304 p = 1) : d1435 p ≤ (2 : Int) + d5244 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1435, d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14081 p hg
    simpa only [d1435, d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1435, d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14061 p hg
    simpa only [d1435, d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14083 (p : Pattern) (guard : d4304 p = 1) : d1436 p ≤ (2 : Int) + d5246 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1436, d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14082 p hg
    simpa only [d1436, d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1436, d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14071 p hg
    simpa only [d1436, d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14084 (p : Pattern) (guard : d4304 p = 1) : d1437 p ≤ (2 : Int) + d5249 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1437, d5249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14083 p hg
    simpa only [d1437, d5249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1437, d5249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14078 p hg
    simpa only [d1437, d5249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14085 (p : Pattern) (guard : d4304 p = 1) : d1438 p ≤ (2 : Int) + d5249 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14079 p hg
    simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14084 p hg
    simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14086 (p : Pattern) (guard : d4147 p = 1) : d105 p ≤ (2 : Int) + d105 p := by
  omega
theorem compare14087 (p : Pattern) (guard : d0 p = 1) : d105 p ≤ (2 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14088 (p : Pattern) (guard : d4147 p = 1) : d110 p ≤ (2 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14087 p hg
    simpa only [d4147, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6163 p hg
    simpa only [d4147, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14089 (p : Pattern) (guard : d4147 p = 1) : d111 p ≤ (2 : Int) + d4339 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d111, d4339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14086 p hg
    simpa only [d111, d4339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d111, d4339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14088 p hg
    simpa only [d111, d4339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14090 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d3 p := by
  change (1 : Int) ≤ (2 : Int) + 3
  decide
theorem compare14091 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (2 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14090 p hg
    simpa only [d102, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d102, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14092 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14090 p hg
    simpa only [d103, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14091 p hg
    simpa only [d103, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14093 (p : Pattern) (guard : d1 p = 1) : d118 p ≤ (2 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d118, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14092 p hg
    simpa only [d118, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d118, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2161 p hg
    simpa only [d118, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14094 (p : Pattern) (guard : d4147 p = 1) : d1043 p ≤ (2 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14087 p hg
    simpa only [d4147, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14093 p hg
    simpa only [d4147, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14095 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14096 (p : Pattern) (guard : d4147 p = 1) : d112 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14095 p hg
    simpa only [d4147, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d4147, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14097 (p : Pattern) (guard : d4147 p = 1) : d1439 p ≤ (2 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1439, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14094 p hg
    simpa only [d1439, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1439, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14096 p hg
    simpa only [d1439, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14098 (p : Pattern) (guard : d4147 p = 1) : d1440 p ≤ (2 : Int) + d4340 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1440, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14089 p hg
    simpa only [d1440, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1440, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14097 p hg
    simpa only [d1440, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14099 (p : Pattern) (guard : d0 p = 1) : d118 p ≤ (2 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14100 (p : Pattern) (guard : d4147 p = 1) : d118 p ≤ (2 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14099 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14093 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14101 (p : Pattern) (guard : d0 p = 1) : d124 p ≤ (2 : Int) + d139 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14102 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (2 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2189 p hg
    simpa only [d125, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d125, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14103 (p : Pattern) (guard : d4147 p = 1) : d126 p ≤ (2 : Int) + d139 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14101 p hg
    simpa only [d4147, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14102 p hg
    simpa only [d4147, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14104 (p : Pattern) (guard : d4147 p = 1) : d1441 p ≤ (2 : Int) + d4341 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1441, d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14100 p hg
    simpa only [d1441, d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1441, d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14103 p hg
    simpa only [d1441, d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14105 (p : Pattern) (guard : d0 p = 1) : d70 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14106 (p : Pattern) (guard : d4147 p = 1) : d128 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14105 p hg
    simpa only [d4147, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d4147, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14107 (p : Pattern) (guard : d4147 p = 1) : d129 p ≤ (2 : Int) + d4342 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d129, d4342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14103 p hg
    simpa only [d129, d4342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d129, d4342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14106 p hg
    simpa only [d129, d4342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14108 (p : Pattern) (guard : d4147 p = 1) : d1442 p ≤ (2 : Int) + d4343 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1442, d4343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14104 p hg
    simpa only [d1442, d4343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1442, d4343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14107 p hg
    simpa only [d1442, d4343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14109 (p : Pattern) (guard : d4147 p = 1) : d1443 p ≤ (2 : Int) + d4344 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1443, d4344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14098 p hg
    simpa only [d1443, d4344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1443, d4344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14108 p hg
    simpa only [d1443, d4344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14110 (p : Pattern) (guard : d0 p = 1) : d1448 p ≤ (2 : Int) + d4344 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14111 (p : Pattern) (guard : d4304 p = 1) : d1449 p ≤ (2 : Int) + d4344 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14109 p hg
    simpa only [d4304, d1449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14110 p hg
    simpa only [d4304, d1449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14112 (p : Pattern) (guard : d4147 p = 1) : d133 p ≤ (2 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14087 p hg
    simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5514 p hg
    simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14113 (p : Pattern) (guard : d4147 p = 1) : d1450 p ≤ (2 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1450, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14112 p hg
    simpa only [d1450, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1450, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14096 p hg
    simpa only [d1450, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14114 (p : Pattern) (guard : d4147 p = 1) : d1451 p ≤ (2 : Int) + d4340 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1451, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14089 p hg
    simpa only [d1451, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1451, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14113 p hg
    simpa only [d1451, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14115 (p : Pattern) (guard : d4147 p = 1) : d1062 p ≤ (2 : Int) + d1062 p := by
  omega
theorem compare14116 (p : Pattern) (guard : d4147 p = 1) : d1452 p ≤ (2 : Int) + d4347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1452, d4347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14114 p hg
    simpa only [d1452, d4347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1452, d4347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14115 p hg
    simpa only [d1452, d4347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14117 (p : Pattern) (guard : d0 p = 1) : d1455 p ≤ (2 : Int) + d4347 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14118 (p : Pattern) (guard : d4304 p = 1) : d1456 p ≤ (2 : Int) + d4347 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14116 p hg
    simpa only [d4304, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14117 p hg
    simpa only [d4304, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14119 (p : Pattern) (guard : d4304 p = 1) : d1457 p ≤ (2 : Int) + d5250 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1457, d5250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14111 p hg
    simpa only [d1457, d5250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1457, d5250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14118 p hg
    simpa only [d1457, d5250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14120 (p : Pattern) (guard : d4147 p = 1) : d159 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14096 p hg
    simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14057 p hg
    simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14121 (p : Pattern) (guard : d4147 p = 1) : d160 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14120 p hg
    simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14057 p hg
    simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14122 (p : Pattern) (guard : d4147 p = 1) : d161 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14121 p hg
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14057 p hg
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14123 (p : Pattern) (guard : d4304 p = 1) : d162 p ≤ (2 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14122 p hg
    simpa only [d4304, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4304, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14124 (p : Pattern) (guard : d4304 p = 1) : d1458 p ≤ (2 : Int) + d5251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1458, d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14118 p hg
    simpa only [d1458, d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1458, d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14123 p hg
    simpa only [d1458, d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14125 (p : Pattern) (guard : d4304 p = 1) : d1459 p ≤ (2 : Int) + d5252 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1459, d5252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14119 p hg
    simpa only [d1459, d5252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1459, d5252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14124 p hg
    simpa only [d1459, d5252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14126 (p : Pattern) (guard : d0 p = 1) : d1461 p ≤ (2 : Int) + d4344 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14127 (p : Pattern) (guard : d4304 p = 1) : d1462 p ≤ (2 : Int) + d4344 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14109 p hg
    simpa only [d4304, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14126 p hg
    simpa only [d4304, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14128 (p : Pattern) (guard : d4304 p = 1) : d1463 p ≤ (2 : Int) + d5250 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1463, d5250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14127 p hg
    simpa only [d1463, d5250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1463, d5250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14118 p hg
    simpa only [d1463, d5250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14129 (p : Pattern) (guard : d4304 p = 1) : d1464 p ≤ (2 : Int) + d5251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1464, d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14118 p hg
    simpa only [d1464, d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1464, d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14076 p hg
    simpa only [d1464, d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14130 (p : Pattern) (guard : d4304 p = 1) : d1465 p ≤ (2 : Int) + d5252 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1465, d5252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14128 p hg
    simpa only [d1465, d5252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1465, d5252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14129 p hg
    simpa only [d1465, d5252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14131 (p : Pattern) (guard : d4304 p = 1) : d1466 p ≤ (2 : Int) + d5252 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14125 p hg
    simpa only [d1466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14130 p hg
    simpa only [d1466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14132 (p : Pattern) (guard : d4304 p = 1) : d1467 p ≤ (2 : Int) + d5253 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1467, d5253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14079 p hg
    simpa only [d1467, d5253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1467, d5253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14131 p hg
    simpa only [d1467, d5253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14133 (p : Pattern) (guard : d4304 p = 1) : d1468 p ≤ (2 : Int) + d5254 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1468, d5254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14085 p hg
    simpa only [d1468, d5254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1468, d5254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14132 p hg
    simpa only [d1468, d5254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14134 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (2 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14027 p hg
    simpa only [d15, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d15, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14135 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (2 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14027 p hg
    simpa only [d16, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14134 p hg
    simpa only [d16, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14136 (p : Pattern) (guard : d4147 p = 1) : d16 p ≤ (2 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14022 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14135 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14137 (p : Pattern) (guard : d4147 p = 1) : d22 p ≤ (2 : Int) + d53 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14136 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14023 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14138 (p : Pattern) (guard : d4147 p = 1) : d1412 p ≤ (2 : Int) + d4361 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1412, d4361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14137 p hg
    simpa only [d1412, d4361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1412, d4361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14051 p hg
    simpa only [d1412, d4361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14139 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (2 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
