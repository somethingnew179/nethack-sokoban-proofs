import NetHack.Soko22Hazard87.Compare011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3000 (p : Pattern) (guard : d4485 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d1228 p = 1 := by simpa only [d4485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2999 p hg
    simpa only [d4485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3001 (p : Pattern) (guard : d1320 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2998 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3002 (p : Pattern) (guard : d1321 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3001 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3003 (p : Pattern) (guard : d4486 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4485 p = 1 := by simpa only [d4486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3000 p hg
    simpa only [d4486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1321 p = 1 := by simpa only [d4486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3002 p hg
    simpa only [d4486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3004 (p : Pattern) (guard : d51736 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d1198 p = 1 := by simpa only [d51736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2978 p hg
    simpa only [d51736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4486 p = 1 := by simpa only [d51736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3003 p hg
    simpa only [d51736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3005 (p : Pattern) (guard : d51737 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d1189 p = 1 := by simpa only [d51737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2969 p hg
    simpa only [d51737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51736 p = 1 := by simpa only [d51737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3004 p hg
    simpa only [d51737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3006 (p : Pattern) (guard : d51738 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51738, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d51738, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51737 p = 1 := by simpa only [d51738, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3005 p hg
    simpa only [d51738, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3007 (p : Pattern) (guard : d51737 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare3008 (p : Pattern) (guard : d1326 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1182 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2960 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3009 (p : Pattern) (guard : d1327 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1184 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2964 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3010 (p : Pattern) (guard : d1328 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3008 p hg
    simpa only [d1328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1327 p = 1 := by simpa only [d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3009 p hg
    simpa only [d1328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3011 (p : Pattern) (guard : d1329 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1328 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3010 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3012 (p : Pattern) (guard : d1330 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3011 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3013 (p : Pattern) (guard : d1331 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1330 p = 1 := by simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3012 p hg
    simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3014 (p : Pattern) (guard : d1332 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1191 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2971 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3015 (p : Pattern) (guard : d1333 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1194 p = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2974 p hg
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3016 (p : Pattern) (guard : d1334 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3014 p hg
    simpa only [d1334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3015 p hg
    simpa only [d1334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3017 (p : Pattern) (guard : d1335 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1334 p = 1 := by simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3016 p hg
    simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3018 (p : Pattern) (guard : d1336 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3017 p hg
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3019 (p : Pattern) (guard : d1337 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1226 p = 1 := by simpa only [d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2995 p hg
    simpa only [d1337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3020 (p : Pattern) (guard : d1171 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1157 p = 1 := by simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2997 p hg
    simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3021 (p : Pattern) (guard : d1338 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3019 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3020 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3022 (p : Pattern) (guard : d4490 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d1338 p = 1 := by simpa only [d4490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3021 p hg
    simpa only [d4490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3023 (p : Pattern) (guard : d1343 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3020 p hg
    simpa only [d1343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3024 (p : Pattern) (guard : d1344 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d1343 p = 1 := by simpa only [d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3023 p hg
    simpa only [d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3025 (p : Pattern) (guard : d4491 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4490 p = 1 := by simpa only [d4491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3022 p hg
    simpa only [d4491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1344 p = 1 := by simpa only [d4491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3024 p hg
    simpa only [d4491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3026 (p : Pattern) (guard : d51739 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d51739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3018 p hg
    simpa only [d51739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4491 p = 1 := by simpa only [d51739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3025 p hg
    simpa only [d51739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3027 (p : Pattern) (guard : d51740 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d51740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3013 p hg
    simpa only [d51740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51739 p = 1 := by simpa only [d51740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3026 p hg
    simpa only [d51740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3028 (p : Pattern) (guard : d51741 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51737 p = 1 := by simpa only [d51741, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3007 p hg
    simpa only [d51741, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51740 p = 1 := by simpa only [d51741, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3027 p hg
    simpa only [d51741, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3029 (p : Pattern) (guard : d51742 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d51738 p = 1 := by simpa only [d51742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3006 p hg
    simpa only [d51742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51741 p = 1 := by simpa only [d51742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3028 p hg
    simpa only [d51742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3030 (p : Pattern) (guard : d1161 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1160 p = 1 := by simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2963 p hg
    simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3031 (p : Pattern) (guard : d1162 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1161 p = 1 := by simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3030 p hg
    simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3032 (p : Pattern) (guard : d1350 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1162 p = 1 := by simpa only [d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3031 p hg
    simpa only [d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3033 (p : Pattern) (guard : d1351 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1350 p = 1 := by simpa only [d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3032 p hg
    simpa only [d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3034 (p : Pattern) (guard : d1352 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1351 p = 1 := by simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3033 p hg
    simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3035 (p : Pattern) (guard : d1353 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1352 p = 1 := by simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3034 p hg
    simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3036 (p : Pattern) (guard : d1354 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1353 p = 1 := by simpa only [d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3035 p hg
    simpa only [d1354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3037 (p : Pattern) (guard : d1355 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1355, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2379 p hg
    simpa only [d1355, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1354 p = 1 := by simpa only [d1355, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3036 p hg
    simpa only [d1355, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3038 (p : Pattern) (guard : d1354 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare3039 (p : Pattern) (guard : d1172 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1161 p = 1 := by simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3030 p hg
    simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3040 (p : Pattern) (guard : d1356 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3039 p hg
    simpa only [d1356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3041 (p : Pattern) (guard : d1357 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1356 p = 1 := by simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3040 p hg
    simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3042 (p : Pattern) (guard : d1358 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1357 p = 1 := by simpa only [d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3041 p hg
    simpa only [d1358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3043 (p : Pattern) (guard : d1359 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1358 p = 1 := by simpa only [d1359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3042 p hg
    simpa only [d1359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3044 (p : Pattern) (guard : d1360 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1359 p = 1 := by simpa only [d1360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3043 p hg
    simpa only [d1360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3045 (p : Pattern) (guard : d1361 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1354 p = 1 := by simpa only [d1361, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3038 p hg
    simpa only [d1361, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1360 p = 1 := by simpa only [d1361, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3044 p hg
    simpa only [d1361, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3046 (p : Pattern) (guard : d1362 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d1355 p = 1 := by simpa only [d1362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3037 p hg
    simpa only [d1362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1361 p = 1 := by simpa only [d1362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3045 p hg
    simpa only [d1362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3047 (p : Pattern) (guard : d51743 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d51742 p = 1 := by simpa only [d51743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3029 p hg
    simpa only [d51743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1362 p = 1 := by simpa only [d51743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3046 p hg
    simpa only [d51743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3048 (p : Pattern) (guard : d51744 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d51743 p = 1 := by simpa only [d51744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3047 p hg
    simpa only [d51744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d51744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3049 (p : Pattern) (guard : d64454 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d64454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51744 p = 1 := by simpa only [d64454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3048 p hg
    simpa only [d64454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3050 (p : Pattern) (guard : d64455 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d64454 p = 1 := by simpa only [d64455, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3049 p hg
    simpa only [d64455, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64455, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d64455, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3051 (p : Pattern) (guard : d64456 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d64455 p = 1 := by simpa only [d64456, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3050 p hg
    simpa only [d64456, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64456, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d64456, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3052 (p : Pattern) (guard : d64457 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64456 p = 1 := by simpa only [d64457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3051 p hg
    simpa only [d64457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3053 (p : Pattern) (guard : d64458 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64457 p = 1 := by simpa only [d64458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3052 p hg
    simpa only [d64458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3054 (p : Pattern) (guard : d64459 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64458 p = 1 := by simpa only [d64459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3053 p hg
    simpa only [d64459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3055 (p : Pattern) (guard : d64460 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64459 p = 1 := by simpa only [d64460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3054 p hg
    simpa only [d64460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3056 (p : Pattern) (guard : d64461 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64460 p = 1 := by simpa only [d64461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3055 p hg
    simpa only [d64461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3057 (p : Pattern) (guard : d64462 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64461 p = 1 := by simpa only [d64462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3056 p hg
    simpa only [d64462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3058 (p : Pattern) (guard : d64463 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64462 p = 1 := by simpa only [d64463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3057 p hg
    simpa only [d64463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3059 (p : Pattern) (guard : d64464 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64463 p = 1 := by simpa only [d64464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3058 p hg
    simpa only [d64464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3060 (p : Pattern) (guard : d64465 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d64453 p = 1 := by simpa only [d64465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2918 p hg
    simpa only [d64465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64464 p = 1 := by simpa only [d64465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3059 p hg
    simpa only [d64465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3061 (p : Pattern) (guard : d1555 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d1555, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d1555, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3062 (p : Pattern) (guard : d1556 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1555 p = 1 := by simpa only [d1556, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3061 p hg
    simpa only [d1556, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1556, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d1556, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3063 (p : Pattern) (guard : d1557 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d1557, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3062 p hg
    simpa only [d1557, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3064 (p : Pattern) (guard : d1558 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3063 p hg
    simpa only [d1558, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d1558, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3065 (p : Pattern) (guard : d1570 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare743 p hg
    simpa only [d1570, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d1570, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3066 (p : Pattern) (guard : d1571 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1570 p = 1 := by simpa only [d1571, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3065 p hg
    simpa only [d1571, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1571, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d1571, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3067 (p : Pattern) (guard : d1572 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d1572, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3066 p hg
    simpa only [d1572, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3068 (p : Pattern) (guard : d1573 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3067 p hg
    simpa only [d1573, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d1573, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3069 (p : Pattern) (guard : d1574 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3064 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1573 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3068 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3070 (p : Pattern) (guard : d1582 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare764 p hg
    simpa only [d1582, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d1582, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3071 (p : Pattern) (guard : d1583 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1582 p = 1 := by simpa only [d1583, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3070 p hg
    simpa only [d1583, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1583, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d1583, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3072 (p : Pattern) (guard : d1584 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d1584, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3071 p hg
    simpa only [d1584, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3073 (p : Pattern) (guard : d1585 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d1585, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d1585, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3074 (p : Pattern) (guard : d1586 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3068 p hg
    simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1585 p = 1 := by simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3073 p hg
    simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3075 (p : Pattern) (guard : d1587 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1574 p = 1 := by simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3069 p hg
    simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1586 p = 1 := by simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3074 p hg
    simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3076 (p : Pattern) (guard : d1588 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3073 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3077 (p : Pattern) (guard : d1589 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1586 p = 1 := by simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3074 p hg
    simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1588 p = 1 := by simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3076 p hg
    simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3078 (p : Pattern) (guard : d1590 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1587 p = 1 := by simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3075 p hg
    simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1589 p = 1 := by simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3077 p hg
    simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3079 (p : Pattern) (guard : d1591 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1591, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d1591, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1590 p = 1 := by simpa only [d1591, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3078 p hg
    simpa only [d1591, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3080 (p : Pattern) (guard : d1592 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1592, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d1592, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1591 p = 1 := by simpa only [d1592, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3079 p hg
    simpa only [d1592, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3081 (p : Pattern) (guard : d1597 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1596 p = 1 := by simpa only [d1597, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare788 p hg
    simpa only [d1597, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1597, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d1597, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3082 (p : Pattern) (guard : d1598 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1597 p = 1 := by simpa only [d1598, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3081 p hg
    simpa only [d1598, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1598, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d1598, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3083 (p : Pattern) (guard : d1599 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1599, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d1599, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1598 p = 1 := by simpa only [d1599, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3082 p hg
    simpa only [d1599, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3084 (p : Pattern) (guard : d1600 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1599 p = 1 := by simpa only [d1600, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3083 p hg
    simpa only [d1600, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1600, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d1600, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3085 (p : Pattern) (guard : d1601 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1600 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3084 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3086 (p : Pattern) (guard : d1602 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3076 p hg
    simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1601 p = 1 := by simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3085 p hg
    simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3087 (p : Pattern) (guard : d1603 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1589 p = 1 := by simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3077 p hg
    simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1602 p = 1 := by simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3086 p hg
    simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3088 (p : Pattern) (guard : d1604 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1604, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d1604, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1603 p = 1 := by simpa only [d1604, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3087 p hg
    simpa only [d1604, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3089 (p : Pattern) (guard : d1605 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1605, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d1605, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1604 p = 1 := by simpa only [d1605, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3088 p hg
    simpa only [d1605, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3090 (p : Pattern) (guard : d1606 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1592 p = 1 := by simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3080 p hg
    simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1605 p = 1 := by simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3089 p hg
    simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3091 (p : Pattern) (guard : d1607 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1605 p = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3089 p hg
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3092 (p : Pattern) (guard : d1608 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1606 p = 1 := by simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3090 p hg
    simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1607 p = 1 := by simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3091 p hg
    simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3093 (p : Pattern) (guard : d1609 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1608 p = 1 := by simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3092 p hg
    simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3094 (p : Pattern) (guard : d1610 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1609 p = 1 := by simpa only [d1610, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3093 p hg
    simpa only [d1610, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1610, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d1610, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3095 (p : Pattern) (guard : d1611 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1611, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d1611, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1610 p = 1 := by simpa only [d1611, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3094 p hg
    simpa only [d1611, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3096 (p : Pattern) (guard : d1612 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1607 p = 1 := by simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3091 p hg
    simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3097 (p : Pattern) (guard : d1613 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1612 p = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3096 p hg
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3098 (p : Pattern) (guard : d1614 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1613 p = 1 := by simpa only [d1614, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3097 p hg
    simpa only [d1614, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1614, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d1614, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3099 (p : Pattern) (guard : d1615 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1615, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d1615, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1614 p = 1 := by simpa only [d1615, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3098 p hg
    simpa only [d1615, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3100 (p : Pattern) (guard : d1616 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1611 p = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3095 p hg
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1615 p = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3099 p hg
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3101 (p : Pattern) (guard : d1617 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1616 p = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3100 p hg
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3102 (p : Pattern) (guard : d1643 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1617 p = 1 := by simpa only [d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3101 p hg
    simpa only [d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3103 (p : Pattern) (guard : d1644 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1643 p = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3102 p hg
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3104 (p : Pattern) (guard : d1620 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1615 p = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3099 p hg
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3105 (p : Pattern) (guard : d1621 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1620 p = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3104 p hg
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3106 (p : Pattern) (guard : d1645 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1621 p = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3105 p hg
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3107 (p : Pattern) (guard : d1646 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1645 p = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3106 p hg
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3108 (p : Pattern) (guard : d1647 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1644 p = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3103 p hg
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1646 p = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3107 p hg
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3109 (p : Pattern) (guard : d1648 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1647 p = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3108 p hg
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3110 (p : Pattern) (guard : d1649 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1648 p = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3109 p hg
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3111 (p : Pattern) (guard : d1650 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1649 p = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3110 p hg
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3112 (p : Pattern) (guard : d1651 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1616 p = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3100 p hg
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3113 (p : Pattern) (guard : d1652 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1651 p = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3112 p hg
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3114 (p : Pattern) (guard : d1653 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1652 p = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3113 p hg
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3115 (p : Pattern) (guard : d1654 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1620 p = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3104 p hg
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3116 (p : Pattern) (guard : d1655 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1654 p = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3115 p hg
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3117 (p : Pattern) (guard : d1656 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1655 p = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3116 p hg
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3118 (p : Pattern) (guard : d1657 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1653 p = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3114 p hg
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1656 p = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3117 p hg
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3119 (p : Pattern) (guard : d1658 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1657 p = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3118 p hg
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3120 (p : Pattern) (guard : d1659 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1658 p = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3119 p hg
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3121 (p : Pattern) (guard : d1665 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1664 p = 1 := by simpa only [d1665, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d1665, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1665, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d1665, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3122 (p : Pattern) (guard : d1666 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1665 p = 1 := by simpa only [d1666, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3121 p hg
    simpa only [d1666, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1666, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d1666, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3123 (p : Pattern) (guard : d1667 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1667, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d1667, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1666 p = 1 := by simpa only [d1667, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3122 p hg
    simpa only [d1667, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3124 (p : Pattern) (guard : d1668 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1667 p = 1 := by simpa only [d1668, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3123 p hg
    simpa only [d1668, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1668, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d1668, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3125 (p : Pattern) (guard : d1669 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1668 p = 1 := by simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3124 p hg
    simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1558 p = 1 := by simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3064 p hg
    simpa only [d1669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3126 (p : Pattern) (guard : d1670 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1669 p = 1 := by simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3125 p hg
    simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1574 p = 1 := by simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3069 p hg
    simpa only [d1670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3127 (p : Pattern) (guard : d1671 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1670 p = 1 := by simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3126 p hg
    simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1587 p = 1 := by simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3075 p hg
    simpa only [d1671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3128 (p : Pattern) (guard : d1672 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1672, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d1672, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1671 p = 1 := by simpa only [d1672, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3127 p hg
    simpa only [d1672, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3129 (p : Pattern) (guard : d1673 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1673, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d1673, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1672 p = 1 := by simpa only [d1673, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3128 p hg
    simpa only [d1673, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3130 (p : Pattern) (guard : d1674 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1673 p = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3129 p hg
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1592 p = 1 := by simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3080 p hg
    simpa only [d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3131 (p : Pattern) (guard : d1675 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1674 p = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3130 p hg
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1606 p = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3090 p hg
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3132 (p : Pattern) (guard : d1676 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1675 p = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3131 p hg
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3133 (p : Pattern) (guard : d1677 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1676 p = 1 := by simpa only [d1677, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3132 p hg
    simpa only [d1677, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1677, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d1677, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3134 (p : Pattern) (guard : d1678 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1678, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d1678, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1677 p = 1 := by simpa only [d1678, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3133 p hg
    simpa only [d1678, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3135 (p : Pattern) (guard : d1679 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1678 p = 1 := by simpa only [d1679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3134 p hg
    simpa only [d1679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1611 p = 1 := by simpa only [d1679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3095 p hg
    simpa only [d1679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3136 (p : Pattern) (guard : d1680 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1679 p = 1 := by simpa only [d1680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3135 p hg
    simpa only [d1680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3137 (p : Pattern) (guard : d1681 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1680 p = 1 := by simpa only [d1681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3136 p hg
    simpa only [d1681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3138 (p : Pattern) (guard : d1682 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1681 p = 1 := by simpa only [d1682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3137 p hg
    simpa only [d1682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3139 (p : Pattern) (guard : d1618 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1617 p = 1 := by simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3101 p hg
    simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3140 (p : Pattern) (guard : d1619 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1618 p = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3139 p hg
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3141 (p : Pattern) (guard : d1683 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1682 p = 1 := by simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3138 p hg
    simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1619 p = 1 := by simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3140 p hg
    simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3142 (p : Pattern) (guard : d4525 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d1683 p = 1 := by simpa only [d4525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3141 p hg
    simpa only [d4525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3143 (p : Pattern) (guard : d1797 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1619 p = 1 := by simpa only [d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3140 p hg
    simpa only [d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3144 (p : Pattern) (guard : d1798 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d1797 p = 1 := by simpa only [d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3143 p hg
    simpa only [d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3145 (p : Pattern) (guard : d4526 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4525 p = 1 := by simpa only [d4526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3142 p hg
    simpa only [d4526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1798 p = 1 := by simpa only [d4526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3144 p hg
    simpa only [d4526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3146 (p : Pattern) (guard : d51764 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d1659 p = 1 := by simpa only [d51764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3120 p hg
    simpa only [d51764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4526 p = 1 := by simpa only [d51764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3145 p hg
    simpa only [d51764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3147 (p : Pattern) (guard : d51765 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d1650 p = 1 := by simpa only [d51765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3111 p hg
    simpa only [d51765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51764 p = 1 := by simpa only [d51765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3146 p hg
    simpa only [d51765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3148 (p : Pattern) (guard : d51766 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51766, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d51766, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51765 p = 1 := by simpa only [d51766, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3147 p hg
    simpa only [d51766, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3149 (p : Pattern) (guard : d51765 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare3150 (p : Pattern) (guard : d1803 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1643 p = 1 := by simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3102 p hg
    simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3151 (p : Pattern) (guard : d1804 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1645 p = 1 := by simpa only [d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3106 p hg
    simpa only [d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3152 (p : Pattern) (guard : d1805 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1803 p = 1 := by simpa only [d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3150 p hg
    simpa only [d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1804 p = 1 := by simpa only [d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3151 p hg
    simpa only [d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3153 (p : Pattern) (guard : d1806 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1805 p = 1 := by simpa only [d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3152 p hg
    simpa only [d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3154 (p : Pattern) (guard : d1807 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1806 p = 1 := by simpa only [d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3153 p hg
    simpa only [d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3155 (p : Pattern) (guard : d1808 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1807 p = 1 := by simpa only [d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3154 p hg
    simpa only [d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3156 (p : Pattern) (guard : d1809 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1652 p = 1 := by simpa only [d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3113 p hg
    simpa only [d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3157 (p : Pattern) (guard : d1810 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1655 p = 1 := by simpa only [d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3116 p hg
    simpa only [d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3158 (p : Pattern) (guard : d1811 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1809 p = 1 := by simpa only [d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3156 p hg
    simpa only [d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1810 p = 1 := by simpa only [d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3157 p hg
    simpa only [d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3159 (p : Pattern) (guard : d1812 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1811 p = 1 := by simpa only [d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3158 p hg
    simpa only [d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3160 (p : Pattern) (guard : d1813 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1812 p = 1 := by simpa only [d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3161 (p : Pattern) (guard : d1814 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1681 p = 1 := by simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3137 p hg
    simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3162 (p : Pattern) (guard : d1632 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1618 p = 1 := by simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3139 p hg
    simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3163 (p : Pattern) (guard : d1815 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1814 p = 1 := by simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3161 p hg
    simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1632 p = 1 := by simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3162 p hg
    simpa only [d1815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3164 (p : Pattern) (guard : d4530 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d1815 p = 1 := by simpa only [d4530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3163 p hg
    simpa only [d4530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3165 (p : Pattern) (guard : d1820 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1632 p = 1 := by simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3162 p hg
    simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3166 (p : Pattern) (guard : d1821 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d1820 p = 1 := by simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3165 p hg
    simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3167 (p : Pattern) (guard : d4531 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4530 p = 1 := by simpa only [d4531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3164 p hg
    simpa only [d4531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1821 p = 1 := by simpa only [d4531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3166 p hg
    simpa only [d4531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3168 (p : Pattern) (guard : d51767 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d1813 p = 1 := by simpa only [d51767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3160 p hg
    simpa only [d51767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4531 p = 1 := by simpa only [d51767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3167 p hg
    simpa only [d51767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3169 (p : Pattern) (guard : d51768 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d1808 p = 1 := by simpa only [d51768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3155 p hg
    simpa only [d51768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51767 p = 1 := by simpa only [d51768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3168 p hg
    simpa only [d51768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3170 (p : Pattern) (guard : d51769 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51765 p = 1 := by simpa only [d51769, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3149 p hg
    simpa only [d51769, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51768 p = 1 := by simpa only [d51769, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3169 p hg
    simpa only [d51769, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3171 (p : Pattern) (guard : d51770 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d51766 p = 1 := by simpa only [d51770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3148 p hg
    simpa only [d51770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51769 p = 1 := by simpa only [d51770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3170 p hg
    simpa only [d51770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3172 (p : Pattern) (guard : d1622 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1621 p = 1 := by simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3105 p hg
    simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3173 (p : Pattern) (guard : d1623 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1622 p = 1 := by simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3172 p hg
    simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3174 (p : Pattern) (guard : d1827 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1623 p = 1 := by simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3173 p hg
    simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3175 (p : Pattern) (guard : d1828 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1827 p = 1 := by simpa only [d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3174 p hg
    simpa only [d1828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3176 (p : Pattern) (guard : d1829 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1828 p = 1 := by simpa only [d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3175 p hg
    simpa only [d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3177 (p : Pattern) (guard : d1830 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1829 p = 1 := by simpa only [d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3176 p hg
    simpa only [d1830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3178 (p : Pattern) (guard : d1831 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1830 p = 1 := by simpa only [d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3177 p hg
    simpa only [d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3179 (p : Pattern) (guard : d1832 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1628 p = 1 := by simpa only [d1832, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2396 p hg
    simpa only [d1832, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1831 p = 1 := by simpa only [d1832, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3178 p hg
    simpa only [d1832, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3180 (p : Pattern) (guard : d1831 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  omega
theorem compare3181 (p : Pattern) (guard : d1633 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1622 p = 1 := by simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3172 p hg
    simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3182 (p : Pattern) (guard : d1833 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1633 p = 1 := by simpa only [d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3181 p hg
    simpa only [d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3183 (p : Pattern) (guard : d1834 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1833 p = 1 := by simpa only [d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3182 p hg
    simpa only [d1834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3184 (p : Pattern) (guard : d1835 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1834 p = 1 := by simpa only [d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3183 p hg
    simpa only [d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3185 (p : Pattern) (guard : d1836 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1835 p = 1 := by simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3184 p hg
    simpa only [d1836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3186 (p : Pattern) (guard : d1837 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1836 p = 1 := by simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3185 p hg
    simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3187 (p : Pattern) (guard : d1838 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1831 p = 1 := by simpa only [d1838, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3180 p hg
    simpa only [d1838, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1837 p = 1 := by simpa only [d1838, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3186 p hg
    simpa only [d1838, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3188 (p : Pattern) (guard : d1839 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d1832 p = 1 := by simpa only [d1839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3179 p hg
    simpa only [d1839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1838 p = 1 := by simpa only [d1839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3187 p hg
    simpa only [d1839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3189 (p : Pattern) (guard : d51771 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d51770 p = 1 := by simpa only [d51771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3171 p hg
    simpa only [d51771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1839 p = 1 := by simpa only [d51771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3188 p hg
    simpa only [d51771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3190 (p : Pattern) (guard : d51772 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d51771 p = 1 := by simpa only [d51772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3189 p hg
    simpa only [d51772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d51772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3191 (p : Pattern) (guard : d64466 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d64466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51772 p = 1 := by simpa only [d64466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3190 p hg
    simpa only [d64466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3192 (p : Pattern) (guard : d64467 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d64466 p = 1 := by simpa only [d64467, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3191 p hg
    simpa only [d64467, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64467, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d64467, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3193 (p : Pattern) (guard : d64468 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d64467 p = 1 := by simpa only [d64468, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3192 p hg
    simpa only [d64468, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64468, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d64468, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3194 (p : Pattern) (guard : d64469 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64468 p = 1 := by simpa only [d64469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3193 p hg
    simpa only [d64469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3195 (p : Pattern) (guard : d64470 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64469 p = 1 := by simpa only [d64470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3194 p hg
    simpa only [d64470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3196 (p : Pattern) (guard : d64471 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64470 p = 1 := by simpa only [d64471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3195 p hg
    simpa only [d64471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3197 (p : Pattern) (guard : d64472 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64471 p = 1 := by simpa only [d64472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3196 p hg
    simpa only [d64472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3198 (p : Pattern) (guard : d64473 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64472 p = 1 := by simpa only [d64473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3197 p hg
    simpa only [d64473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3199 (p : Pattern) (guard : d64474 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64473 p = 1 := by simpa only [d64474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3198 p hg
    simpa only [d64474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3200 (p : Pattern) (guard : d64475 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64474 p = 1 := by simpa only [d64475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d64475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3201 (p : Pattern) (guard : d64476 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64475 p = 1 := by simpa only [d64476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3200 p hg
    simpa only [d64476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3202 (p : Pattern) (guard : d64477 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d64477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d64477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64476 p = 1 := by simpa only [d64477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3201 p hg
    simpa only [d64477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3203 (p : Pattern) (guard : d64478 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d64465 p = 1 := by simpa only [d64478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3060 p hg
    simpa only [d64478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64477 p = 1 := by simpa only [d64478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3202 p hg
    simpa only [d64478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3204 (p : Pattern) (guard : d2035 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare938 p hg
    simpa only [d2035, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d2035, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3205 (p : Pattern) (guard : d2036 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2035 p = 1 := by simpa only [d2036, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3204 p hg
    simpa only [d2036, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2036, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d2036, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3206 (p : Pattern) (guard : d2037 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2037, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d2037, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2037, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3205 p hg
    simpa only [d2037, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3207 (p : Pattern) (guard : d2038 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3206 p hg
    simpa only [d2038, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d2038, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3208 (p : Pattern) (guard : d2053 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare972 p hg
    simpa only [d2053, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d2053, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3209 (p : Pattern) (guard : d2054 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2053 p = 1 := by simpa only [d2054, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3208 p hg
    simpa only [d2054, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2054, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d2054, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3210 (p : Pattern) (guard : d2055 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d2055, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3209 p hg
    simpa only [d2055, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3211 (p : Pattern) (guard : d2056 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3210 p hg
    simpa only [d2056, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d2056, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3212 (p : Pattern) (guard : d2057 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3207 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2056 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3211 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3213 (p : Pattern) (guard : d2065 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare993 p hg
    simpa only [d2065, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d2065, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3214 (p : Pattern) (guard : d2066 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2065 p = 1 := by simpa only [d2066, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3213 p hg
    simpa only [d2066, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2066, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d2066, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3215 (p : Pattern) (guard : d2067 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d2067, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3214 p hg
    simpa only [d2067, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3216 (p : Pattern) (guard : d2068 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3215 p hg
    simpa only [d2068, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d2068, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3217 (p : Pattern) (guard : d2069 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3211 p hg
    simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2068 p = 1 := by simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3216 p hg
    simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3218 (p : Pattern) (guard : d2070 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2057 p = 1 := by simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3212 p hg
    simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2069 p = 1 := by simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3217 p hg
    simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3219 (p : Pattern) (guard : d2071 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3216 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3220 (p : Pattern) (guard : d2072 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2069 p = 1 := by simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3217 p hg
    simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2071 p = 1 := by simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3219 p hg
    simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3221 (p : Pattern) (guard : d2073 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2070 p = 1 := by simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3218 p hg
    simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2072 p = 1 := by simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3220 p hg
    simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3222 (p : Pattern) (guard : d2074 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2074, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d2074, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2073 p = 1 := by simpa only [d2074, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3221 p hg
    simpa only [d2074, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3223 (p : Pattern) (guard : d2075 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2075, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d2075, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2074 p = 1 := by simpa only [d2075, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3222 p hg
    simpa only [d2075, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3224 (p : Pattern) (guard : d2080 p = 1) : d47660 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2079 p = 1 := by simpa only [d2080, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1017 p hg
    simpa only [d2080, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2080, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d2080, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3225 (p : Pattern) (guard : d2081 p = 1) : d47663 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2080 p = 1 := by simpa only [d2081, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3224 p hg
    simpa only [d2081, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2081, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d2081, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3226 (p : Pattern) (guard : d2082 p = 1) : d47664 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2082, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d2082, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2081 p = 1 := by simpa only [d2082, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3225 p hg
    simpa only [d2082, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3227 (p : Pattern) (guard : d2083 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2082 p = 1 := by simpa only [d2083, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3226 p hg
    simpa only [d2083, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2083, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d2083, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3228 (p : Pattern) (guard : d2084 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2083 p = 1 := by simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3227 p hg
    simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3229 (p : Pattern) (guard : d2085 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3219 p hg
    simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2084 p = 1 := by simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3228 p hg
    simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3230 (p : Pattern) (guard : d2086 p = 1) : d47685 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2072 p = 1 := by simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3220 p hg
    simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2085 p = 1 := by simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3229 p hg
    simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3231 (p : Pattern) (guard : d2087 p = 1) : d47686 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2087, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d2087, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2086 p = 1 := by simpa only [d2087, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3230 p hg
    simpa only [d2087, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3232 (p : Pattern) (guard : d2088 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2088, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d2088, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2087 p = 1 := by simpa only [d2088, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3231 p hg
    simpa only [d2088, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3233 (p : Pattern) (guard : d2089 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2075 p = 1 := by simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3223 p hg
    simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2088 p = 1 := by simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3232 p hg
    simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3234 (p : Pattern) (guard : d2090 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2088 p = 1 := by simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3232 p hg
    simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3235 (p : Pattern) (guard : d2091 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2089 p = 1 := by simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3233 p hg
    simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2090 p = 1 := by simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3234 p hg
    simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3236 (p : Pattern) (guard : d2092 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2091 p = 1 := by simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3235 p hg
    simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3237 (p : Pattern) (guard : d2093 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2092 p = 1 := by simpa only [d2093, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3236 p hg
    simpa only [d2093, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2093, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d2093, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3238 (p : Pattern) (guard : d2094 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2094, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d2094, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2093 p = 1 := by simpa only [d2094, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3237 p hg
    simpa only [d2094, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3239 (p : Pattern) (guard : d2095 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2090 p = 1 := by simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3234 p hg
    simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3240 (p : Pattern) (guard : d2096 p = 1) : d47687 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2095 p = 1 := by simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3239 p hg
    simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3241 (p : Pattern) (guard : d2097 p = 1) : d47699 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2096 p = 1 := by simpa only [d2097, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3240 p hg
    simpa only [d2097, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2097, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d2097, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3242 (p : Pattern) (guard : d2098 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2098, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d2098, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2097 p = 1 := by simpa only [d2098, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3241 p hg
    simpa only [d2098, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3243 (p : Pattern) (guard : d2099 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2094 p = 1 := by simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3238 p hg
    simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2098 p = 1 := by simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3242 p hg
    simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3244 (p : Pattern) (guard : d2100 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d2099 p = 1 := by simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3243 p hg
    simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3245 (p : Pattern) (guard : d2126 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2100 p = 1 := by simpa only [d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3244 p hg
    simpa only [d2126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3246 (p : Pattern) (guard : d2127 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2126 p = 1 := by simpa only [d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3245 p hg
    simpa only [d2127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3247 (p : Pattern) (guard : d2103 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2098 p = 1 := by simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3242 p hg
    simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3248 (p : Pattern) (guard : d2104 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d2103 p = 1 := by simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3247 p hg
    simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3249 (p : Pattern) (guard : d2128 p = 1) : d47700 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2104 p = 1 := by simpa only [d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3248 p hg
    simpa only [d2128, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
