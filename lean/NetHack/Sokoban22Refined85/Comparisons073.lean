/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons072
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10220 (p : Pattern) (guard : d4397 p = 1) : d1291 p ≤ (0 : Int) + d1051 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1291, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9951 p hg
    simpa only [d4397, d1291, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1291, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10219 p hg
    simpa only [d4397, d1291, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10221 (p : Pattern) (guard : d4397 p = 1) : d1292 p ≤ (0 : Int) + d1054 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1292, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9955 p hg
    simpa only [d4397, d1292, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1292, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1292, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10222 (p : Pattern) (guard : d4397 p = 1) : d1293 p ≤ (0 : Int) + d1055 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1293, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10220 p hg
    simpa only [d1293, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1293, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10221 p hg
    simpa only [d1293, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10223 (p : Pattern) (guard : d4397 p = 1) : d1294 p ≤ (0 : Int) + d1056 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1294, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10218 p hg
    simpa only [d1294, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1294, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10222 p hg
    simpa only [d1294, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10224 (p : Pattern) (guard : d4397 p = 1) : d1295 p ≤ (0 : Int) + d1057 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1295, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10214 p hg
    simpa only [d1295, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1295, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10223 p hg
    simpa only [d1295, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10225 (p : Pattern) (guard : d0 p = 1) : d1296 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10226 (p : Pattern) (guard : d4397 p = 1) : d1297 p ≤ (0 : Int) + d1058 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1297, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9459 p hg
    simpa only [d4397, d1297, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1297, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10225 p hg
    simpa only [d4397, d1297, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10227 (p : Pattern) (guard : d4397 p = 1) : d1298 p ≤ (0 : Int) + d1059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1298, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9961 p hg
    simpa only [d4397, d1298, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1298, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d4397, d1298, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10228 (p : Pattern) (guard : d4397 p = 1) : d1299 p ≤ (0 : Int) + d1060 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1299, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10226 p hg
    simpa only [d1299, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1299, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10227 p hg
    simpa only [d1299, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10229 (p : Pattern) (guard : d4397 p = 1) : d1300 p ≤ (0 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1300, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9964 p hg
    simpa only [d4397, d1300, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1300, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1300, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10230 (p : Pattern) (guard : d4397 p = 1) : d1301 p ≤ (0 : Int) + d1062 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1301, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10229 p hg
    simpa only [d1301, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1301, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1301, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10231 (p : Pattern) (guard : d4397 p = 1) : d1302 p ≤ (0 : Int) + d1063 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1302, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10228 p hg
    simpa only [d1302, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1302, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10230 p hg
    simpa only [d1302, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10232 (p : Pattern) (guard : d0 p = 1) : d1289 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10233 (p : Pattern) (guard : d4397 p = 1) : d1304 p ≤ (0 : Int) + d1059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1304, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9969 p hg
    simpa only [d4397, d1304, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1304, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10232 p hg
    simpa only [d4397, d1304, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10234 (p : Pattern) (guard : d4397 p = 1) : d1300 p ≤ (0 : Int) + d1064 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1300, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9972 p hg
    simpa only [d4397, d1300, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1300, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1300, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10235 (p : Pattern) (guard : d4397 p = 1) : d1305 p ≤ (0 : Int) + d1065 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1305, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10233 p hg
    simpa only [d1305, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1305, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10234 p hg
    simpa only [d1305, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10236 (p : Pattern) (guard : d4397 p = 1) : d1301 p ≤ (0 : Int) + d1066 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1301, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10234 p hg
    simpa only [d1301, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1301, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1301, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10237 (p : Pattern) (guard : d4397 p = 1) : d1306 p ≤ (0 : Int) + d1067 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1306, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10235 p hg
    simpa only [d1306, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1306, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10236 p hg
    simpa only [d1306, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10238 (p : Pattern) (guard : d4397 p = 1) : d1307 p ≤ (0 : Int) + d1068 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1307, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10231 p hg
    simpa only [d1307, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1307, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10237 p hg
    simpa only [d1307, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10239 (p : Pattern) (guard : d4397 p = 1) : d1308 p ≤ (0 : Int) + d1069 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1308, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10224 p hg
    simpa only [d1308, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1308, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10238 p hg
    simpa only [d1308, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10240 (p : Pattern) (guard : d0 p = 1) : d1296 p ≤ (0 : Int) + d361 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10241 (p : Pattern) (guard : d4397 p = 1) : d1309 p ≤ (0 : Int) + d1070 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1309, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9472 p hg
    simpa only [d4397, d1309, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1309, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10240 p hg
    simpa only [d4397, d1309, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10242 (p : Pattern) (guard : d4397 p = 1) : d1310 p ≤ (0 : Int) + d1071 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1310, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10241 p hg
    simpa only [d1310, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1310, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10227 p hg
    simpa only [d1310, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10243 (p : Pattern) (guard : d4397 p = 1) : d1311 p ≤ (0 : Int) + d1072 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1311, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10242 p hg
    simpa only [d1311, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1311, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10230 p hg
    simpa only [d1311, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10244 (p : Pattern) (guard : d0 p = 1) : d1289 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10245 (p : Pattern) (guard : d4397 p = 1) : d1313 p ≤ (0 : Int) + d1073 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1313, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9982 p hg
    simpa only [d4397, d1313, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1313, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10244 p hg
    simpa only [d4397, d1313, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10246 (p : Pattern) (guard : d4397 p = 1) : d1314 p ≤ (0 : Int) + d1074 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1314, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10245 p hg
    simpa only [d1314, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1314, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10234 p hg
    simpa only [d1314, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10247 (p : Pattern) (guard : d4397 p = 1) : d1315 p ≤ (0 : Int) + d1075 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1315, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10246 p hg
    simpa only [d1315, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1315, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10236 p hg
    simpa only [d1315, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10248 (p : Pattern) (guard : d4397 p = 1) : d1316 p ≤ (0 : Int) + d1076 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1316, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10243 p hg
    simpa only [d1316, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1316, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10247 p hg
    simpa only [d1316, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10249 (p : Pattern) (guard : d4397 p = 1) : d1317 p ≤ (0 : Int) + d1077 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1317, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10248 p hg
    simpa only [d1317, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1317, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8258 p hg
    simpa only [d1317, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10250 (p : Pattern) (guard : d4397 p = 1) : d1318 p ≤ (0 : Int) + d1078 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1318, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10239 p hg
    simpa only [d1318, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1318, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10249 p hg
    simpa only [d1318, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10251 (p : Pattern) (guard : d0 p = 1) : d1303 p ≤ (0 : Int) + d389 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10252 (p : Pattern) (guard : d4397 p = 1) : d1320 p ≤ (0 : Int) + d1079 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1320, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9481 p hg
    simpa only [d4397, d1320, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1320, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10251 p hg
    simpa only [d4397, d1320, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10253 (p : Pattern) (guard : d4397 p = 1) : d1298 p ≤ (0 : Int) + d1080 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1298, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9991 p hg
    simpa only [d4397, d1298, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1298, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d4397, d1298, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10254 (p : Pattern) (guard : d4397 p = 1) : d1321 p ≤ (0 : Int) + d1081 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1321, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10252 p hg
    simpa only [d1321, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1321, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10253 p hg
    simpa only [d1321, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10255 (p : Pattern) (guard : d0 p = 1) : d1278 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10256 (p : Pattern) (guard : d4397 p = 1) : d1323 p ≤ (0 : Int) + d1082 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1323, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9994 p hg
    simpa only [d4397, d1323, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1323, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10255 p hg
    simpa only [d4397, d1323, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10257 (p : Pattern) (guard : d4397 p = 1) : d1324 p ≤ (0 : Int) + d1083 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1324, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10256 p hg
    simpa only [d1324, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1324, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10212 p hg
    simpa only [d1324, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10258 (p : Pattern) (guard : d4397 p = 1) : d1325 p ≤ (0 : Int) + d1084 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1325, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10254 p hg
    simpa only [d1325, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1325, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10257 p hg
    simpa only [d1325, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10259 (p : Pattern) (guard : d0 p = 1) : d1289 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10260 (p : Pattern) (guard : d4397 p = 1) : d1326 p ≤ (0 : Int) + d1085 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1326, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9999 p hg
    simpa only [d4397, d1326, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1326, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10259 p hg
    simpa only [d4397, d1326, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10261 (p : Pattern) (guard : d4397 p = 1) : d1300 p ≤ (0 : Int) + d1051 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1300, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9951 p hg
    simpa only [d4397, d1300, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1300, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1300, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10262 (p : Pattern) (guard : d4397 p = 1) : d1327 p ≤ (0 : Int) + d1086 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1327, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10260 p hg
    simpa only [d1327, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1327, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10261 p hg
    simpa only [d1327, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10263 (p : Pattern) (guard : d4397 p = 1) : d1328 p ≤ (0 : Int) + d1087 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1328, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10262 p hg
    simpa only [d1328, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1328, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10222 p hg
    simpa only [d1328, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10264 (p : Pattern) (guard : d4397 p = 1) : d1329 p ≤ (0 : Int) + d1088 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1329, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10258 p hg
    simpa only [d1329, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1329, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10263 p hg
    simpa only [d1329, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10265 (p : Pattern) (guard : d0 p = 1) : d1296 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10266 (p : Pattern) (guard : d4397 p = 1) : d1296 p ≤ (0 : Int) + d1089 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9494 p hg
    simpa only [d4397, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10265 p hg
    simpa only [d4397, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10267 (p : Pattern) (guard : d4397 p = 1) : d1330 p ≤ (0 : Int) + d1090 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1330, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10266 p hg
    simpa only [d1330, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1330, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10227 p hg
    simpa only [d1330, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10268 (p : Pattern) (guard : d4397 p = 1) : d1331 p ≤ (0 : Int) + d1091 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1331, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10267 p hg
    simpa only [d1331, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1331, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10230 p hg
    simpa only [d1331, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10269 (p : Pattern) (guard : d4397 p = 1) : d1332 p ≤ (0 : Int) + d1059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1332, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9961 p hg
    simpa only [d4397, d1332, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1332, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10232 p hg
    simpa only [d4397, d1332, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10270 (p : Pattern) (guard : d4397 p = 1) : d1333 p ≤ (0 : Int) + d1065 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1333, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10269 p hg
    simpa only [d1333, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1333, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10234 p hg
    simpa only [d1333, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10271 (p : Pattern) (guard : d4397 p = 1) : d1334 p ≤ (0 : Int) + d1067 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1334, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10270 p hg
    simpa only [d1334, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1334, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10236 p hg
    simpa only [d1334, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10272 (p : Pattern) (guard : d4397 p = 1) : d1335 p ≤ (0 : Int) + d1092 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1335, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10268 p hg
    simpa only [d1335, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1335, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10271 p hg
    simpa only [d1335, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10273 (p : Pattern) (guard : d4397 p = 1) : d1336 p ≤ (0 : Int) + d1093 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1336, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10264 p hg
    simpa only [d1336, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1336, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10272 p hg
    simpa only [d1336, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10274 (p : Pattern) (guard : d4397 p = 1) : d1337 p ≤ (0 : Int) + d1089 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1337, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9502 p hg
    simpa only [d4397, d1337, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1337, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10265 p hg
    simpa only [d4397, d1337, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10275 (p : Pattern) (guard : d4397 p = 1) : d1338 p ≤ (0 : Int) + d1090 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1338, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10274 p hg
    simpa only [d1338, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1338, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10227 p hg
    simpa only [d1338, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10276 (p : Pattern) (guard : d4397 p = 1) : d1339 p ≤ (0 : Int) + d1091 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1339, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10275 p hg
    simpa only [d1339, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1339, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10230 p hg
    simpa only [d1339, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10277 (p : Pattern) (guard : d4397 p = 1) : d1340 p ≤ (0 : Int) + d1092 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1340, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10276 p hg
    simpa only [d1340, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1340, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10271 p hg
    simpa only [d1340, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10278 (p : Pattern) (guard : d4397 p = 1) : d1341 p ≤ (0 : Int) + d1094 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1341, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10277 p hg
    simpa only [d1341, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1341, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1341, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10279 (p : Pattern) (guard : d4397 p = 1) : d1342 p ≤ (0 : Int) + d1095 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1342, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10273 p hg
    simpa only [d1342, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1342, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10278 p hg
    simpa only [d1342, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10280 (p : Pattern) (guard : d4397 p = 1) : d1343 p ≤ (0 : Int) + d1096 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1343, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10250 p hg
    simpa only [d1343, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1343, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10279 p hg
    simpa only [d1343, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10281 (p : Pattern) (guard : d4397 p = 1) : d1344 p ≤ (0 : Int) + d1097 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1344, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10165 p hg
    simpa only [d1344, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1344, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10280 p hg
    simpa only [d1344, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10282 (p : Pattern) (guard : d4397 p = 1) : d1345 p ≤ (0 : Int) + d1098 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1345, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10205 p hg
    simpa only [d1345, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1345, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10281 p hg
    simpa only [d1345, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10283 (p : Pattern) (guard : d4397 p = 1) : d1181 p ≤ (0 : Int) + d968 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9830 p hg
    simpa only [d4397, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d4397, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10284 (p : Pattern) (guard : d4397 p = 1) : d1346 p ≤ (0 : Int) + d1099 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1346, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10283 p hg
    simpa only [d1346, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1346, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10110 p hg
    simpa only [d1346, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10285 (p : Pattern) (guard : d4397 p = 1) : d1348 p ≤ (0 : Int) + d1100 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1348, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10022 p hg
    simpa only [d4397, d1348, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1348, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1348, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10286 (p : Pattern) (guard : d4397 p = 1) : d1349 p ≤ (0 : Int) + d1101 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1349, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10285 p hg
    simpa only [d1349, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1349, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1349, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10287 (p : Pattern) (guard : d4397 p = 1) : d1350 p ≤ (0 : Int) + d1102 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1350, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10284 p hg
    simpa only [d1350, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1350, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10286 p hg
    simpa only [d1350, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10288 (p : Pattern) (guard : d4397 p = 1) : d1351 p ≤ (0 : Int) + d1103 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1351, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10199 p hg
    simpa only [d1351, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1351, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10287 p hg
    simpa only [d1351, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10289 (p : Pattern) (guard : d4397 p = 1) : d1352 p ≤ (0 : Int) + d1104 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1352, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10196 p hg
    simpa only [d1352, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1352, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10288 p hg
    simpa only [d1352, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10290 (p : Pattern) (guard : d4397 p = 1) : d1353 p ≤ (0 : Int) + d1103 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1353, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10151 p hg
    simpa only [d1353, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1353, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10287 p hg
    simpa only [d1353, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10291 (p : Pattern) (guard : d4397 p = 1) : d1354 p ≤ (0 : Int) + d1105 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1354, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10290 p hg
    simpa only [d1354, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1354, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1354, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10292 (p : Pattern) (guard : d4397 p = 1) : d1355 p ≤ (0 : Int) + d1106 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1355, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10289 p hg
    simpa only [d1355, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1355, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10291 p hg
    simpa only [d1355, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10293 (p : Pattern) (guard : d4397 p = 1) : d1356 p ≤ (0 : Int) + d1107 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1356, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10190 p hg
    simpa only [d1356, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1356, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10292 p hg
    simpa only [d1356, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10294 (p : Pattern) (guard : d4397 p = 1) : d1357 p ≤ (0 : Int) + d1108 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1357, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10165 p hg
    simpa only [d1357, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1357, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10293 p hg
    simpa only [d1357, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10295 (p : Pattern) (guard : d0 p = 1) : d1289 p ≤ (0 : Int) + d448 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10296 (p : Pattern) (guard : d4397 p = 1) : d1358 p ≤ (0 : Int) + d1109 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1358, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9943 p hg
    simpa only [d4397, d1358, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1358, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10295 p hg
    simpa only [d4397, d1358, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10297 (p : Pattern) (guard : d4397 p = 1) : d1359 p ≤ (0 : Int) + d1110 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1359, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10296 p hg
    simpa only [d1359, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1359, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10261 p hg
    simpa only [d1359, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10298 (p : Pattern) (guard : d4397 p = 1) : d1360 p ≤ (0 : Int) + d1111 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1360, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10297 p hg
    simpa only [d1360, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1360, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10222 p hg
    simpa only [d1360, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10299 (p : Pattern) (guard : d4397 p = 1) : d1361 p ≤ (0 : Int) + d1112 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1361, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10214 p hg
    simpa only [d1361, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1361, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10298 p hg
    simpa only [d1361, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10300 (p : Pattern) (guard : d4397 p = 1) : d1362 p ≤ (0 : Int) + d1068 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1362, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10231 p hg
    simpa only [d1362, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1362, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10271 p hg
    simpa only [d1362, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10301 (p : Pattern) (guard : d4397 p = 1) : d1363 p ≤ (0 : Int) + d1113 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1363, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10299 p hg
    simpa only [d1363, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1363, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10300 p hg
    simpa only [d1363, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10302 (p : Pattern) (guard : d4397 p = 1) : d1364 p ≤ (0 : Int) + d1114 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1364, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10243 p hg
    simpa only [d1364, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1364, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10271 p hg
    simpa only [d1364, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10303 (p : Pattern) (guard : d4397 p = 1) : d1365 p ≤ (0 : Int) + d1115 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1365, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10302 p hg
    simpa only [d1365, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1365, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8258 p hg
    simpa only [d1365, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10304 (p : Pattern) (guard : d4397 p = 1) : d1366 p ≤ (0 : Int) + d1116 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1366, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10301 p hg
    simpa only [d1366, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1366, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10303 p hg
    simpa only [d1366, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10305 (p : Pattern) (guard : d0 p = 1) : d1296 p ≤ (0 : Int) + d450 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10306 (p : Pattern) (guard : d4397 p = 1) : d1367 p ≤ (0 : Int) + d1117 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1367, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9481 p hg
    simpa only [d4397, d1367, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1367, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10305 p hg
    simpa only [d4397, d1367, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10307 (p : Pattern) (guard : d4397 p = 1) : d1298 p ≤ (0 : Int) + d1118 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1298, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9543 p hg
    simpa only [d4397, d1298, d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1298, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d4397, d1298, d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10308 (p : Pattern) (guard : d4397 p = 1) : d1368 p ≤ (0 : Int) + d1119 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1368, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10306 p hg
    simpa only [d1368, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1368, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10307 p hg
    simpa only [d1368, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10309 (p : Pattern) (guard : d0 p = 1) : d1370 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10310 (p : Pattern) (guard : d4397 p = 1) : d1371 p ≤ (0 : Int) + d1120 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1371, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10044 p hg
    simpa only [d4397, d1371, d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1371, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10309 p hg
    simpa only [d4397, d1371, d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10311 (p : Pattern) (guard : d4397 p = 1) : d1372 p ≤ (0 : Int) + d1121 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1372, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9535 p hg
    simpa only [d4397, d1372, d1121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1372, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4396 p hg
    simpa only [d4397, d1372, d1121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10312 (p : Pattern) (guard : d4397 p = 1) : d1373 p ≤ (0 : Int) + d1122 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1373, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10310 p hg
    simpa only [d1373, d1122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1373, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10311 p hg
    simpa only [d1373, d1122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10313 (p : Pattern) (guard : d4397 p = 1) : d1374 p ≤ (0 : Int) + d1123 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1374, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10308 p hg
    simpa only [d1374, d1123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1374, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10312 p hg
    simpa only [d1374, d1123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10314 (p : Pattern) (guard : d4397 p = 1) : d1300 p ≤ (0 : Int) + d1124 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1300, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10049 p hg
    simpa only [d4397, d1300, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1300, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1300, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10315 (p : Pattern) (guard : d4397 p = 1) : d1333 p ≤ (0 : Int) + d1125 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1333, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10269 p hg
    simpa only [d1333, d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1333, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10314 p hg
    simpa only [d1333, d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10316 (p : Pattern) (guard : d0 p = 1) : d1375 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10317 (p : Pattern) (guard : d4397 p = 1) : d1376 p ≤ (0 : Int) + d1124 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1376, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10049 p hg
    simpa only [d4397, d1376, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1376, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10316 p hg
    simpa only [d4397, d1376, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10318 (p : Pattern) (guard : d4397 p = 1) : d1377 p ≤ (0 : Int) + d1129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1377, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10055 p hg
    simpa only [d4397, d1377, d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1377, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1377, d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10319 (p : Pattern) (guard : d4397 p = 1) : d1378 p ≤ (0 : Int) + d1130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1378, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10317 p hg
    simpa only [d1378, d1130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1378, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10318 p hg
    simpa only [d1378, d1130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10320 (p : Pattern) (guard : d4397 p = 1) : d1379 p ≤ (0 : Int) + d1131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1379, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10315 p hg
    simpa only [d1379, d1131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1379, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10319 p hg
    simpa only [d1379, d1131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10321 (p : Pattern) (guard : d4397 p = 1) : d1380 p ≤ (0 : Int) + d1132 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1380, d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10313 p hg
    simpa only [d1380, d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1380, d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10320 p hg
    simpa only [d1380, d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10322 (p : Pattern) (guard : d0 p = 1) : d1369 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10323 (p : Pattern) (guard : d4397 p = 1) : d1381 p ≤ (0 : Int) + d1089 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1381, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9494 p hg
    simpa only [d4397, d1381, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1381, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10322 p hg
    simpa only [d4397, d1381, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10324 (p : Pattern) (guard : d4397 p = 1) : d1382 p ≤ (0 : Int) + d1134 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1382, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10061 p hg
    simpa only [d4397, d1382, d1134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1382, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4396 p hg
    simpa only [d4397, d1382, d1134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10325 (p : Pattern) (guard : d4397 p = 1) : d1383 p ≤ (0 : Int) + d1135 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1383, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10323 p hg
    simpa only [d1383, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1383, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10324 p hg
    simpa only [d1383, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10326 (p : Pattern) (guard : d4397 p = 1) : d1384 p ≤ (0 : Int) + d1136 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1384, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10325 p hg
    simpa only [d1384, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1384, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10230 p hg
    simpa only [d1384, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10327 (p : Pattern) (guard : d0 p = 1) : d1385 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10328 (p : Pattern) (guard : d4397 p = 1) : d1386 p ≤ (0 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1386, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9964 p hg
    simpa only [d4397, d1386, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1386, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10327 p hg
    simpa only [d4397, d1386, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10329 (p : Pattern) (guard : d4397 p = 1) : d1387 p ≤ (0 : Int) + d1138 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1387, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10067 p hg
    simpa only [d4397, d1387, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1387, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1387, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10330 (p : Pattern) (guard : d4397 p = 1) : d1388 p ≤ (0 : Int) + d1139 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1388, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10328 p hg
    simpa only [d1388, d1139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1388, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10329 p hg
    simpa only [d1388, d1139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10331 (p : Pattern) (guard : d4397 p = 1) : d213 p ≤ (0 : Int) + d1140 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d213, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2411 p hg
    simpa only [d4397, d213, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d213, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d213, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10332 (p : Pattern) (guard : d4397 p = 1) : d1389 p ≤ (0 : Int) + d1141 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1389, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10331 p hg
    simpa only [d1389, d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1389, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1389, d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10333 (p : Pattern) (guard : d4397 p = 1) : d1390 p ≤ (0 : Int) + d1142 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1390, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10330 p hg
    simpa only [d1390, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1390, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10332 p hg
    simpa only [d1390, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10334 (p : Pattern) (guard : d4397 p = 1) : d1391 p ≤ (0 : Int) + d1143 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1391, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10326 p hg
    simpa only [d1391, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1391, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10333 p hg
    simpa only [d1391, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10335 (p : Pattern) (guard : d4397 p = 1) : d1392 p ≤ (0 : Int) + d1144 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1392, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10321 p hg
    simpa only [d1392, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1392, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10334 p hg
    simpa only [d1392, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10336 (p : Pattern) (guard : d4397 p = 1) : d1393 p ≤ (0 : Int) + d1145 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1393, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10334 p hg
    simpa only [d1393, d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1393, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1393, d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10337 (p : Pattern) (guard : d4397 p = 1) : d1394 p ≤ (0 : Int) + d1146 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1394, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10335 p hg
    simpa only [d1394, d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1394, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10336 p hg
    simpa only [d1394, d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10338 (p : Pattern) (guard : d4397 p = 1) : d1395 p ≤ (0 : Int) + d1147 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1395, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10304 p hg
    simpa only [d1395, d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1395, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10337 p hg
    simpa only [d1395, d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10339 (p : Pattern) (guard : d4397 p = 1) : d1396 p ≤ (0 : Int) + d1148 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1396, d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10165 p hg
    simpa only [d1396, d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1396, d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10338 p hg
    simpa only [d1396, d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10340 (p : Pattern) (guard : d4397 p = 1) : d1397 p ≤ (0 : Int) + d1149 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1397, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10294 p hg
    simpa only [d1397, d1149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1397, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10339 p hg
    simpa only [d1397, d1149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10341 (p : Pattern) (guard : d4397 p = 1) : d1398 p ≤ (0 : Int) + d1150 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1398, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10282 p hg
    simpa only [d1398, d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1398, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10340 p hg
    simpa only [d1398, d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10342 (p : Pattern) (guard : d0 p = 1) : d1151 p ≤ (0 : Int) + d950 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10343 (p : Pattern) (guard : d0 p = 1) : d345 p ≤ (0 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10344 (p : Pattern) (guard : d4148 p = 1) : d1152 p ≤ (0 : Int) + d950 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1152, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1152, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1152, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10343 p hg
    simpa only [d4148, d1152, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10345 (p : Pattern) (guard : d4672 p = 1) : d1153 p ≤ (0 : Int) + d950 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10342 p hg
    simpa only [d4672, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10344 p hg
    simpa only [d4672, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10346 (p : Pattern) (guard : d0 p = 1) : d1155 p ≤ (0 : Int) + d950 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10347 (p : Pattern) (guard : d4673 p = 1) : d1156 p ≤ (0 : Int) + d950 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10345 p hg
    simpa only [d4673, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10346 p hg
    simpa only [d4673, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10348 (p : Pattern) (guard : d0 p = 1) : d1157 p ≤ (0 : Int) + d47 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10349 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d42, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d42, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d42, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare712 p hg
    simpa only [d42, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10350 (p : Pattern) (guard : d4148 p = 1) : d1158 p ≤ (0 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1158, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10349 p hg
    simpa only [d4148, d1158, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1158, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9329 p hg
    simpa only [d4148, d1158, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10351 (p : Pattern) (guard : d4672 p = 1) : d1159 p ≤ (0 : Int) + d47 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10348 p hg
    simpa only [d4672, d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10350 p hg
    simpa only [d4672, d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10352 (p : Pattern) (guard : d0 p = 1) : d1161 p ≤ (0 : Int) + d47 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10353 (p : Pattern) (guard : d4673 p = 1) : d1162 p ≤ (0 : Int) + d47 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10351 p hg
    simpa only [d4673, d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10352 p hg
    simpa only [d4673, d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10354 (p : Pattern) (guard : d4673 p = 1) : d1163 p ≤ (0 : Int) + d4818 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1163, d4818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10347 p hg
    simpa only [d1163, d4818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1163, d4818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10353 p hg
    simpa only [d1163, d4818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10355 (p : Pattern) (guard : d0 p = 1) : d1164 p ≤ (0 : Int) + d796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10356 (p : Pattern) (guard : d0 p = 1) : d360 p ≤ (0 : Int) + d795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10357 (p : Pattern) (guard : d4148 p = 1) : d1165 p ≤ (0 : Int) + d796 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1165, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4148, d1165, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1165, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10356 p hg
    simpa only [d4148, d1165, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10358 (p : Pattern) (guard : d4672 p = 1) : d1166 p ≤ (0 : Int) + d796 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10355 p hg
    simpa only [d4672, d1166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10357 p hg
    simpa only [d4672, d1166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10359 (p : Pattern) (guard : d0 p = 1) : d1168 p ≤ (0 : Int) + d796 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
