/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons058
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8260 (p : Pattern) (guard : d4397 p = 1) : d1078 p ≤ (0 : Int) + d1318 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1078, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8247 p hg
    simpa only [d1078, d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1078, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8259 p hg
    simpa only [d1078, d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8261 (p : Pattern) (guard : d0 p = 1) : d389 p ≤ (0 : Int) + d1303 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8262 (p : Pattern) (guard : d4397 p = 1) : d1079 p ≤ (0 : Int) + d1320 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1079, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3796 p hg
    simpa only [d4397, d1079, d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1079, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8261 p hg
    simpa only [d4397, d1079, d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8263 (p : Pattern) (guard : d0 p = 1) : d118 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8264 (p : Pattern) (guard : d4148 p = 1) : d1043 p ≤ (0 : Int) + d1296 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1043, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1043, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1043, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8263 p hg
    simpa only [d4148, d1043, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8265 (p : Pattern) (guard : d4397 p = 1) : d1080 p ≤ (0 : Int) + d1298 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1080, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8264 p hg
    simpa only [d4397, d1080, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1080, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d4397, d1080, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8266 (p : Pattern) (guard : d4397 p = 1) : d1081 p ≤ (0 : Int) + d1321 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1081, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8262 p hg
    simpa only [d1081, d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1081, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8265 p hg
    simpa only [d1081, d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8267 (p : Pattern) (guard : d4148 p = 1) : d118 p ≤ (0 : Int) + d1322 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4148, d1322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8263 p hg
    simpa only [d4148, d1322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8268 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1278 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8269 (p : Pattern) (guard : d4397 p = 1) : d1082 p ≤ (0 : Int) + d1323 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1082, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8267 p hg
    simpa only [d4397, d1082, d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1082, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8268 p hg
    simpa only [d4397, d1082, d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8270 (p : Pattern) (guard : d4397 p = 1) : d1083 p ≤ (0 : Int) + d1324 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1083, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8269 p hg
    simpa only [d1083, d1324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1083, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8208 p hg
    simpa only [d1083, d1324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8271 (p : Pattern) (guard : d4397 p = 1) : d1084 p ≤ (0 : Int) + d1325 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1084, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8266 p hg
    simpa only [d1084, d1325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1084, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8270 p hg
    simpa only [d1084, d1325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8272 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8273 (p : Pattern) (guard : d4148 p = 1) : d133 p ≤ (0 : Int) + d1274 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d133, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d133, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d133, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8272 p hg
    simpa only [d4148, d133, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8274 (p : Pattern) (guard : d4397 p = 1) : d1085 p ≤ (0 : Int) + d1326 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1085, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8273 p hg
    simpa only [d4397, d1085, d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1085, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7968 p hg
    simpa only [d4397, d1085, d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8275 (p : Pattern) (guard : d4397 p = 1) : d1051 p ≤ (0 : Int) + d1300 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1051, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8219 p hg
    simpa only [d4397, d1051, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1051, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1051, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8276 (p : Pattern) (guard : d4397 p = 1) : d1086 p ≤ (0 : Int) + d1327 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1086, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8274 p hg
    simpa only [d1086, d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1086, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8275 p hg
    simpa only [d1086, d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8277 (p : Pattern) (guard : d4397 p = 1) : d1087 p ≤ (0 : Int) + d1328 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1087, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8276 p hg
    simpa only [d1087, d1328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1087, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8225 p hg
    simpa only [d1087, d1328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8278 (p : Pattern) (guard : d4397 p = 1) : d1088 p ≤ (0 : Int) + d1329 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1088, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8271 p hg
    simpa only [d1088, d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1088, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8277 p hg
    simpa only [d1088, d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8279 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1296 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8280 (p : Pattern) (guard : d4397 p = 1) : d1089 p ≤ (0 : Int) + d1296 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3809 p hg
    simpa only [d4397, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8279 p hg
    simpa only [d4397, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8281 (p : Pattern) (guard : d4397 p = 1) : d1090 p ≤ (0 : Int) + d1330 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1090, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8280 p hg
    simpa only [d1090, d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1090, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8232 p hg
    simpa only [d1090, d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8282 (p : Pattern) (guard : d4397 p = 1) : d1091 p ≤ (0 : Int) + d1331 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1091, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8281 p hg
    simpa only [d1091, d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1091, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8236 p hg
    simpa only [d1091, d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8283 (p : Pattern) (guard : d4397 p = 1) : d1059 p ≤ (0 : Int) + d1332 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1059, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8231 p hg
    simpa only [d4397, d1059, d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1059, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7940 p hg
    simpa only [d4397, d1059, d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8284 (p : Pattern) (guard : d4397 p = 1) : d1065 p ≤ (0 : Int) + d1333 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1065, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8283 p hg
    simpa only [d1065, d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1065, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8242 p hg
    simpa only [d1065, d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8285 (p : Pattern) (guard : d4397 p = 1) : d1067 p ≤ (0 : Int) + d1334 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1067, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8284 p hg
    simpa only [d1067, d1334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1067, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8244 p hg
    simpa only [d1067, d1334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8286 (p : Pattern) (guard : d4397 p = 1) : d1092 p ≤ (0 : Int) + d1335 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1092, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8282 p hg
    simpa only [d1092, d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1092, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8285 p hg
    simpa only [d1092, d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8287 (p : Pattern) (guard : d4397 p = 1) : d1093 p ≤ (0 : Int) + d1336 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1093, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8278 p hg
    simpa only [d1093, d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1093, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8286 p hg
    simpa only [d1093, d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8288 (p : Pattern) (guard : d4397 p = 1) : d1089 p ≤ (0 : Int) + d1337 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1089, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3817 p hg
    simpa only [d4397, d1089, d1337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1089, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8279 p hg
    simpa only [d4397, d1089, d1337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8289 (p : Pattern) (guard : d4397 p = 1) : d1090 p ≤ (0 : Int) + d1338 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1090, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8288 p hg
    simpa only [d1090, d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1090, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8232 p hg
    simpa only [d1090, d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8290 (p : Pattern) (guard : d4397 p = 1) : d1091 p ≤ (0 : Int) + d1339 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1091, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8289 p hg
    simpa only [d1091, d1339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1091, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8236 p hg
    simpa only [d1091, d1339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8291 (p : Pattern) (guard : d4397 p = 1) : d1092 p ≤ (0 : Int) + d1340 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1092, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8290 p hg
    simpa only [d1092, d1340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1092, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8285 p hg
    simpa only [d1092, d1340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8292 (p : Pattern) (guard : d4397 p = 1) : d1094 p ≤ (0 : Int) + d1341 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1094, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8291 p hg
    simpa only [d1094, d1341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1094, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1094, d1341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8293 (p : Pattern) (guard : d4397 p = 1) : d1095 p ≤ (0 : Int) + d1342 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1095, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8287 p hg
    simpa only [d1095, d1342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1095, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8292 p hg
    simpa only [d1095, d1342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8294 (p : Pattern) (guard : d4397 p = 1) : d1096 p ≤ (0 : Int) + d1343 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1096, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8260 p hg
    simpa only [d1096, d1343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1096, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8293 p hg
    simpa only [d1096, d1343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8295 (p : Pattern) (guard : d4397 p = 1) : d1097 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1097, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8150 p hg
    simpa only [d1097, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1097, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8294 p hg
    simpa only [d1097, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8296 (p : Pattern) (guard : d4397 p = 1) : d1098 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1098, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8197 p hg
    simpa only [d1098, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1098, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8295 p hg
    simpa only [d1098, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8297 (p : Pattern) (guard : d4397 p = 1) : d968 p ≤ (0 : Int) + d1181 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8079 p hg
    simpa only [d4397, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7864 p hg
    simpa only [d4397, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8298 (p : Pattern) (guard : d4397 p = 1) : d1099 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1099, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8297 p hg
    simpa only [d1099, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1099, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8087 p hg
    simpa only [d1099, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8299 (p : Pattern) (guard : d4148 p = 1) : d20 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare847 p hg
    simpa only [d4148, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3640 p hg
    simpa only [d4148, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8300 (p : Pattern) (guard : d4397 p = 1) : d1100 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1100, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8299 p hg
    simpa only [d4397, d1100, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1100, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1100, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8301 (p : Pattern) (guard : d4397 p = 1) : d1101 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1101, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8300 p hg
    simpa only [d1101, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1101, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1101, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8302 (p : Pattern) (guard : d4397 p = 1) : d1102 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1102, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8298 p hg
    simpa only [d1102, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1102, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8301 p hg
    simpa only [d1102, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8303 (p : Pattern) (guard : d4397 p = 1) : d1103 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1103, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8191 p hg
    simpa only [d1103, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1103, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8302 p hg
    simpa only [d1103, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8304 (p : Pattern) (guard : d4397 p = 1) : d1104 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1104, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8188 p hg
    simpa only [d1104, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1104, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8303 p hg
    simpa only [d1104, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8305 (p : Pattern) (guard : d4397 p = 1) : d1103 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1103, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8137 p hg
    simpa only [d1103, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1103, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8302 p hg
    simpa only [d1103, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8306 (p : Pattern) (guard : d4397 p = 1) : d1105 p ≤ (0 : Int) + d1354 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1105, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8305 p hg
    simpa only [d1105, d1354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1105, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1105, d1354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8307 (p : Pattern) (guard : d4397 p = 1) : d1106 p ≤ (0 : Int) + d1355 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1106, d1355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8304 p hg
    simpa only [d1106, d1355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1106, d1355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8306 p hg
    simpa only [d1106, d1355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8308 (p : Pattern) (guard : d4397 p = 1) : d1107 p ≤ (0 : Int) + d1356 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1107, d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8181 p hg
    simpa only [d1107, d1356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1107, d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8307 p hg
    simpa only [d1107, d1356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8309 (p : Pattern) (guard : d4397 p = 1) : d1108 p ≤ (0 : Int) + d1357 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1108, d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8150 p hg
    simpa only [d1108, d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1108, d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8308 p hg
    simpa only [d1108, d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8310 (p : Pattern) (guard : d4397 p = 1) : d1109 p ≤ (0 : Int) + d1358 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1109, d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8212 p hg
    simpa only [d4397, d1109, d1358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1109, d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7994 p hg
    simpa only [d4397, d1109, d1358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8311 (p : Pattern) (guard : d4397 p = 1) : d1110 p ≤ (0 : Int) + d1359 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1110, d1359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8310 p hg
    simpa only [d1110, d1359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1110, d1359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8275 p hg
    simpa only [d1110, d1359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8312 (p : Pattern) (guard : d4397 p = 1) : d1111 p ≤ (0 : Int) + d1360 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1111, d1360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8311 p hg
    simpa only [d1111, d1360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1111, d1360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8225 p hg
    simpa only [d1111, d1360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8313 (p : Pattern) (guard : d4397 p = 1) : d1112 p ≤ (0 : Int) + d1361 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1112, d1361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8210 p hg
    simpa only [d1112, d1361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1112, d1361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8312 p hg
    simpa only [d1112, d1361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8314 (p : Pattern) (guard : d4397 p = 1) : d1068 p ≤ (0 : Int) + d1362 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1068, d1362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8237 p hg
    simpa only [d1068, d1362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1068, d1362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8285 p hg
    simpa only [d1068, d1362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8315 (p : Pattern) (guard : d4397 p = 1) : d1113 p ≤ (0 : Int) + d1363 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1113, d1363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8313 p hg
    simpa only [d1113, d1363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1113, d1363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8314 p hg
    simpa only [d1113, d1363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8316 (p : Pattern) (guard : d4397 p = 1) : d1114 p ≤ (0 : Int) + d1364 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1114, d1364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8251 p hg
    simpa only [d1114, d1364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1114, d1364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8285 p hg
    simpa only [d1114, d1364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8317 (p : Pattern) (guard : d4397 p = 1) : d1115 p ≤ (0 : Int) + d1365 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1115, d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8316 p hg
    simpa only [d1115, d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1115, d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8258 p hg
    simpa only [d1115, d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8318 (p : Pattern) (guard : d4397 p = 1) : d1116 p ≤ (0 : Int) + d1366 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1116, d1366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8315 p hg
    simpa only [d1116, d1366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1116, d1366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8317 p hg
    simpa only [d1116, d1366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8319 (p : Pattern) (guard : d0 p = 1) : d450 p ≤ (0 : Int) + d1296 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8320 (p : Pattern) (guard : d4397 p = 1) : d1117 p ≤ (0 : Int) + d1367 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1117, d1367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3796 p hg
    simpa only [d4397, d1117, d1367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1117, d1367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8319 p hg
    simpa only [d4397, d1117, d1367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8321 (p : Pattern) (guard : d4397 p = 1) : d1118 p ≤ (0 : Int) + d1298 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1118, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3861 p hg
    simpa only [d4397, d1118, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1118, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d4397, d1118, d1298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8322 (p : Pattern) (guard : d4397 p = 1) : d1119 p ≤ (0 : Int) + d1368 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1119, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8320 p hg
    simpa only [d1119, d1368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1119, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8321 p hg
    simpa only [d1119, d1368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8323 (p : Pattern) (guard : d4148 p = 1) : d269 p ≤ (0 : Int) + d1369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4148, d1369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3860 p hg
    simpa only [d4148, d1369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8324 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8325 (p : Pattern) (guard : d4397 p = 1) : d1120 p ≤ (0 : Int) + d1371 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1120, d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8323 p hg
    simpa only [d4397, d1120, d1371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1120, d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8324 p hg
    simpa only [d4397, d1120, d1371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8326 (p : Pattern) (guard : d4397 p = 1) : d1121 p ≤ (0 : Int) + d1372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1121, d1372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3852 p hg
    simpa only [d4397, d1121, d1372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1121, d1372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8011 p hg
    simpa only [d4397, d1121, d1372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8327 (p : Pattern) (guard : d4397 p = 1) : d1122 p ≤ (0 : Int) + d1373 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1122, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8325 p hg
    simpa only [d1122, d1373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1122, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8326 p hg
    simpa only [d1122, d1373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8328 (p : Pattern) (guard : d4397 p = 1) : d1123 p ≤ (0 : Int) + d1374 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1123, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8322 p hg
    simpa only [d1123, d1374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1123, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8327 p hg
    simpa only [d1123, d1374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8329 (p : Pattern) (guard : d0 p = 1) : d298 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8330 (p : Pattern) (guard : d4148 p = 1) : d925 p ≤ (0 : Int) + d1289 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d925, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4148, d925, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d925, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8329 p hg
    simpa only [d4148, d925, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8331 (p : Pattern) (guard : d4397 p = 1) : d1124 p ≤ (0 : Int) + d1300 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1124, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8330 p hg
    simpa only [d4397, d1124, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1124, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1124, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8332 (p : Pattern) (guard : d4397 p = 1) : d1125 p ≤ (0 : Int) + d1333 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1125, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8283 p hg
    simpa only [d1125, d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1125, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8331 p hg
    simpa only [d1125, d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8333 (p : Pattern) (guard : d4397 p = 1) : d1124 p ≤ (0 : Int) + d1376 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1124, d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8330 p hg
    simpa only [d4397, d1124, d1376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1124, d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8017 p hg
    simpa only [d4397, d1124, d1376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8334 (p : Pattern) (guard : d1 p = 1) : d283 p ≤ (0 : Int) + d283 p := by
  omega
theorem compare8335 (p : Pattern) (guard : d0 p = 1) : d1127 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8336 (p : Pattern) (guard : d4148 p = 1) : d1128 p ≤ (0 : Int) + d1375 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1128, d1375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8334 p hg
    simpa only [d4148, d1128, d1375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1128, d1375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8335 p hg
    simpa only [d4148, d1128, d1375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8337 (p : Pattern) (guard : d4397 p = 1) : d1129 p ≤ (0 : Int) + d1377 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1129, d1377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8336 p hg
    simpa only [d4397, d1129, d1377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1129, d1377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1129, d1377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8338 (p : Pattern) (guard : d4397 p = 1) : d1130 p ≤ (0 : Int) + d1378 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1130, d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8333 p hg
    simpa only [d1130, d1378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1130, d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8337 p hg
    simpa only [d1130, d1378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8339 (p : Pattern) (guard : d4397 p = 1) : d1131 p ≤ (0 : Int) + d1379 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1131, d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8332 p hg
    simpa only [d1131, d1379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1131, d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8338 p hg
    simpa only [d1131, d1379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8340 (p : Pattern) (guard : d4397 p = 1) : d1132 p ≤ (0 : Int) + d1380 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1132, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8328 p hg
    simpa only [d1132, d1380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1132, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8339 p hg
    simpa only [d1132, d1380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8341 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1369 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8342 (p : Pattern) (guard : d4397 p = 1) : d1089 p ≤ (0 : Int) + d1381 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1089, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3809 p hg
    simpa only [d4397, d1089, d1381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1089, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8341 p hg
    simpa only [d4397, d1089, d1381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8343 (p : Pattern) (guard : d4148 p = 1) : d1133 p ≤ (0 : Int) + d1369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1133, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4148, d1133, d1369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1133, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8230 p hg
    simpa only [d4148, d1133, d1369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8344 (p : Pattern) (guard : d4397 p = 1) : d1134 p ≤ (0 : Int) + d1382 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1134, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8343 p hg
    simpa only [d4397, d1134, d1382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1134, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8011 p hg
    simpa only [d4397, d1134, d1382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8345 (p : Pattern) (guard : d4397 p = 1) : d1135 p ≤ (0 : Int) + d1383 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1135, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8342 p hg
    simpa only [d1135, d1383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1135, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8344 p hg
    simpa only [d1135, d1383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8346 (p : Pattern) (guard : d4397 p = 1) : d1136 p ≤ (0 : Int) + d1384 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1136, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8345 p hg
    simpa only [d1136, d1384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1136, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8236 p hg
    simpa only [d1136, d1384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8347 (p : Pattern) (guard : d4397 p = 1) : d1061 p ≤ (0 : Int) + d1386 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1061, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8234 p hg
    simpa only [d4397, d1061, d1386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1061, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d4397, d1061, d1386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8348 (p : Pattern) (guard : d1 p = 1) : d298 p ≤ (0 : Int) + d298 p := by
  omega
theorem compare8349 (p : Pattern) (guard : d4148 p = 1) : d1137 p ≤ (0 : Int) + d1385 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1137, d1385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8348 p hg
    simpa only [d4148, d1137, d1385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1137, d1385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3772 p hg
    simpa only [d4148, d1137, d1385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8350 (p : Pattern) (guard : d4397 p = 1) : d1138 p ≤ (0 : Int) + d1387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1138, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8349 p hg
    simpa only [d4397, d1138, d1387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1138, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1138, d1387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8351 (p : Pattern) (guard : d4397 p = 1) : d1139 p ≤ (0 : Int) + d1388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1139, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8347 p hg
    simpa only [d1139, d1388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1139, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8350 p hg
    simpa only [d1139, d1388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8352 (p : Pattern) (guard : d4148 p = 1) : d109 p ≤ (0 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d4148, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3772 p hg
    simpa only [d4148, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8353 (p : Pattern) (guard : d4397 p = 1) : d1140 p ≤ (0 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1140, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8352 p hg
    simpa only [d4397, d1140, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1140, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1140, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8354 (p : Pattern) (guard : d4397 p = 1) : d1141 p ≤ (0 : Int) + d1389 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1141, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8353 p hg
    simpa only [d1141, d1389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1141, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1141, d1389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8355 (p : Pattern) (guard : d4397 p = 1) : d1142 p ≤ (0 : Int) + d1390 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1142, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8351 p hg
    simpa only [d1142, d1390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1142, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8354 p hg
    simpa only [d1142, d1390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8356 (p : Pattern) (guard : d4397 p = 1) : d1143 p ≤ (0 : Int) + d1391 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1143, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8346 p hg
    simpa only [d1143, d1391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1143, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8355 p hg
    simpa only [d1143, d1391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8357 (p : Pattern) (guard : d4397 p = 1) : d1144 p ≤ (0 : Int) + d1392 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1144, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8340 p hg
    simpa only [d1144, d1392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1144, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8356 p hg
    simpa only [d1144, d1392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8358 (p : Pattern) (guard : d4397 p = 1) : d1145 p ≤ (0 : Int) + d1393 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1145, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8356 p hg
    simpa only [d1145, d1393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1145, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1145, d1393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8359 (p : Pattern) (guard : d4397 p = 1) : d1146 p ≤ (0 : Int) + d1394 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1146, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8357 p hg
    simpa only [d1146, d1394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1146, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8358 p hg
    simpa only [d1146, d1394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8360 (p : Pattern) (guard : d4397 p = 1) : d1147 p ≤ (0 : Int) + d1395 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1147, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8318 p hg
    simpa only [d1147, d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1147, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8359 p hg
    simpa only [d1147, d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8361 (p : Pattern) (guard : d4397 p = 1) : d1148 p ≤ (0 : Int) + d1396 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1148, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8150 p hg
    simpa only [d1148, d1396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1148, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8360 p hg
    simpa only [d1148, d1396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8362 (p : Pattern) (guard : d4397 p = 1) : d1149 p ≤ (0 : Int) + d1397 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1149, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8309 p hg
    simpa only [d1149, d1397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1149, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8361 p hg
    simpa only [d1149, d1397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8363 (p : Pattern) (guard : d4397 p = 1) : d1150 p ≤ (0 : Int) + d1398 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1150, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8296 p hg
    simpa only [d1150, d1398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1150, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8362 p hg
    simpa only [d1150, d1398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8364 (p : Pattern) (guard : d0 p = 1) : d346 p ≤ (4 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8365 (p : Pattern) (guard : d4765 p = 1) : d949 p ≤ (4 : Int) + d16 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3877 p hg
    simpa only [d4765, d949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8364 p hg
    simpa only [d4765, d949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8366 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (4 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2507 p hg
    simpa only [d33, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2644 p hg
    simpa only [d33, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8367 (p : Pattern) (guard : d4147 p = 1) : d950 p ≤ (4 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3878 p hg
    simpa only [d4147, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8366 p hg
    simpa only [d4147, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8368 (p : Pattern) (guard : d0 p = 1) : d361 p ≤ (4 : Int) + d26 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8369 (p : Pattern) (guard : d4765 p = 1) : d951 p ≤ (4 : Int) + d4305 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d951, d4305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8367 p hg
    simpa only [d4765, d951, d4305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d951, d4305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8368 p hg
    simpa only [d4765, d951, d4305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8370 (p : Pattern) (guard : d4765 p = 1) : d952 p ≤ (4 : Int) + d4306 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d952, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8365 p hg
    simpa only [d952, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d952, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8369 p hg
    simpa only [d952, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8371 (p : Pattern) (guard : d4147 p = 1) : d33 p ≤ (4 : Int) + d33 p := by
  omega
theorem compare8372 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (4 : Int) + d42 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8373 (p : Pattern) (guard : d4765 p = 1) : d953 p ≤ (4 : Int) + d4307 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d953, d4307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8371 p hg
    simpa only [d4765, d953, d4307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d953, d4307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8372 p hg
    simpa only [d4765, d953, d4307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8374 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d48 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8375 (p : Pattern) (guard : d4765 p = 1) : d954 p ≤ (4 : Int) + d4308 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d954, d4308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3898 p hg
    simpa only [d4765, d954, d4308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d954, d4308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8374 p hg
    simpa only [d4765, d954, d4308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8376 (p : Pattern) (guard : d4765 p = 1) : d955 p ≤ (4 : Int) + d4309 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d955, d4309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8373 p hg
    simpa only [d955, d4309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d955, d4309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8375 p hg
    simpa only [d955, d4309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8377 (p : Pattern) (guard : d4765 p = 1) : d956 p ≤ (4 : Int) + d4310 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d956, d4310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8370 p hg
    simpa only [d956, d4310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d956, d4310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8376 p hg
    simpa only [d956, d4310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8378 (p : Pattern) (guard : d4147 p = 1) : d54 p ≤ (4 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3878 p hg
    simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2645 p hg
    simpa only [d4147, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8379 (p : Pattern) (guard : d0 p = 1) : d369 p ≤ (4 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8380 (p : Pattern) (guard : d4765 p = 1) : d957 p ≤ (4 : Int) + d4311 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d957, d4311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8378 p hg
    simpa only [d4765, d957, d4311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d957, d4311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8379 p hg
    simpa only [d4765, d957, d4311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8381 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (4 : Int) + d2 p := by
  change (4 : Int) ≤ (4 : Int) + 2
  decide
theorem compare8382 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (4 : Int) + d30 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8381 p hg
    simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8383 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (4 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8381 p hg
    simpa only [d18, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8382 p hg
    simpa only [d18, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8384 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (4 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8383 p hg
    simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8385 (p : Pattern) (guard : d1 p = 1) : d795 p ≤ (4 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d795, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2550 p hg
    simpa only [d795, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d795, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8384 p hg
    simpa only [d795, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8386 (p : Pattern) (guard : d4147 p = 1) : d796 p ≤ (4 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3907 p hg
    simpa only [d4147, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8385 p hg
    simpa only [d4147, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8387 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (4 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8388 (p : Pattern) (guard : d4765 p = 1) : d958 p ≤ (4 : Int) + d4312 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d958, d4312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8386 p hg
    simpa only [d4765, d958, d4312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d958, d4312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8387 p hg
    simpa only [d4765, d958, d4312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8389 (p : Pattern) (guard : d4765 p = 1) : d959 p ≤ (4 : Int) + d4313 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d959, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8380 p hg
    simpa only [d959, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d959, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8388 p hg
    simpa only [d959, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8390 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8391 (p : Pattern) (guard : d4765 p = 1) : d960 p ≤ (4 : Int) + d4314 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d960, d4314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8386 p hg
    simpa only [d4765, d960, d4314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d960, d4314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8390 p hg
    simpa only [d4765, d960, d4314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8392 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (4 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8393 (p : Pattern) (guard : d1 p = 1) : d173 p ≤ (4 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d173, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2515 p hg
    simpa only [d173, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d173, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d173, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8394 (p : Pattern) (guard : d4147 p = 1) : d176 p ≤ (4 : Int) + d66 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8392 p hg
    simpa only [d4147, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8393 p hg
    simpa only [d4147, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8395 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d72 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8396 (p : Pattern) (guard : d4765 p = 1) : d961 p ≤ (4 : Int) + d4315 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d961, d4315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8394 p hg
    simpa only [d4765, d961, d4315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d961, d4315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8395 p hg
    simpa only [d4765, d961, d4315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8397 (p : Pattern) (guard : d4765 p = 1) : d962 p ≤ (4 : Int) + d4316 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d962, d4316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8391 p hg
    simpa only [d962, d4316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d962, d4316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8396 p hg
    simpa only [d962, d4316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8398 (p : Pattern) (guard : d4765 p = 1) : d963 p ≤ (4 : Int) + d4317 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d963, d4317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8389 p hg
    simpa only [d963, d4317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d963, d4317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8397 p hg
    simpa only [d963, d4317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8399 (p : Pattern) (guard : d4765 p = 1) : d964 p ≤ (4 : Int) + d4318 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d964, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8377 p hg
    simpa only [d964, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d964, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8398 p hg
    simpa only [d964, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
