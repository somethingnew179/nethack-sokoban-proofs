/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1260 (p : Pattern) (guard : d985 p = 1) : d46 p ≤ (0 : Int) + d999 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d46, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1228 p hg
    simpa only [d46, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d46, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1238 p hg
    simpa only [d46, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1261 (p : Pattern) (guard : d985 p = 1) : d47 p ≤ (0 : Int) + d1000 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d47, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1228 p hg
    simpa only [d47, d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d47, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1260 p hg
    simpa only [d47, d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1262 (p : Pattern) (guard : d985 p = 1) : d48 p ≤ (0 : Int) + d1001 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d48, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1228 p hg
    simpa only [d48, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d48, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1248 p hg
    simpa only [d48, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1263 (p : Pattern) (guard : d985 p = 1) : d49 p ≤ (0 : Int) + d999 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d49, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1255 p hg
    simpa only [d49, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d49, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1238 p hg
    simpa only [d49, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1264 (p : Pattern) (guard : d985 p = 1) : d50 p ≤ (0 : Int) + d1002 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d50, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1262 p hg
    simpa only [d50, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d50, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1263 p hg
    simpa only [d50, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1265 (p : Pattern) (guard : d985 p = 1) : d51 p ≤ (0 : Int) + d1003 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d51, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1261 p hg
    simpa only [d51, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d51, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1264 p hg
    simpa only [d51, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1266 (p : Pattern) (guard : d985 p = 1) : d52 p ≤ (0 : Int) + d701 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1220 p hg
    simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d52, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1267 (p : Pattern) (guard : d985 p = 1) : d53 p ≤ (0 : Int) + d702 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1228 p hg
    simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1266 p hg
    simpa only [d53, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1268 (p : Pattern) (guard : d985 p = 1) : d54 p ≤ (0 : Int) + d1004 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d54, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1233 p hg
    simpa only [d54, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d54, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d54, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1269 (p : Pattern) (guard : d985 p = 1) : d55 p ≤ (0 : Int) + d1005 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d55, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1238 p hg
    simpa only [d55, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d55, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1268 p hg
    simpa only [d55, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1270 (p : Pattern) (guard : d985 p = 1) : d56 p ≤ (0 : Int) + d1006 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d56, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1267 p hg
    simpa only [d56, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d56, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1269 p hg
    simpa only [d56, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1271 (p : Pattern) (guard : d985 p = 1) : d57 p ≤ (0 : Int) + d1007 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d57, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1267 p hg
    simpa only [d57, d1007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d57, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1270 p hg
    simpa only [d57, d1007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1272 (p : Pattern) (guard : d985 p = 1) : d58 p ≤ (0 : Int) + d1008 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d58, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d58, d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d58, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d58, d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1273 (p : Pattern) (guard : d985 p = 1) : d59 p ≤ (0 : Int) + d1009 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d59, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1248 p hg
    simpa only [d59, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d59, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1272 p hg
    simpa only [d59, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1274 (p : Pattern) (guard : d985 p = 1) : d60 p ≤ (0 : Int) + d1010 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d60, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1267 p hg
    simpa only [d60, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d60, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1273 p hg
    simpa only [d60, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1275 (p : Pattern) (guard : d985 p = 1) : d61 p ≤ (0 : Int) + d701 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d61, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1252 p hg
    simpa only [d61, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d61, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d61, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1276 (p : Pattern) (guard : d985 p = 1) : d62 p ≤ (0 : Int) + d702 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d62, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1255 p hg
    simpa only [d62, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d62, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1275 p hg
    simpa only [d62, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1277 (p : Pattern) (guard : d985 p = 1) : d63 p ≤ (0 : Int) + d1006 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d63, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1276 p hg
    simpa only [d63, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d63, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1269 p hg
    simpa only [d63, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1278 (p : Pattern) (guard : d985 p = 1) : d64 p ≤ (0 : Int) + d1011 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d64, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d64, d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d64, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d64, d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1279 (p : Pattern) (guard : d985 p = 1) : d65 p ≤ (0 : Int) + d1012 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d65, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1271 p hg
    simpa only [d65, d1012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d65, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1278 p hg
    simpa only [d65, d1012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1280 (p : Pattern) (guard : d985 p = 1) : d66 p ≤ (0 : Int) + d1013 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d66, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1265 p hg
    simpa only [d66, d1013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d66, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1279 p hg
    simpa only [d66, d1013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1281 (p : Pattern) (guard : d985 p = 1) : d67 p ≤ (0 : Int) + d1014 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d67, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1259 p hg
    simpa only [d67, d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d67, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1280 p hg
    simpa only [d67, d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1282 (p : Pattern) (guard : d985 p = 1) : d68 p ≤ (0 : Int) + d705 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d68, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d68, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d68, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d68, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1283 (p : Pattern) (guard : d985 p = 1) : d69 p ≤ (0 : Int) + d706 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d69, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d69, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d69, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d69, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1284 (p : Pattern) (guard : d985 p = 1) : d70 p ≤ (0 : Int) + d1015 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d70, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1237 p hg
    simpa only [d70, d1015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d70, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d70, d1015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1285 (p : Pattern) (guard : d985 p = 1) : d71 p ≤ (0 : Int) + d1016 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d71, d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1237 p hg
    simpa only [d71, d1016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d71, d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1284 p hg
    simpa only [d71, d1016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1286 (p : Pattern) (guard : d985 p = 1) : d72 p ≤ (0 : Int) + d1017 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d72, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1283 p hg
    simpa only [d72, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d72, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1285 p hg
    simpa only [d72, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1287 (p : Pattern) (guard : d985 p = 1) : d73 p ≤ (0 : Int) + d1018 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d73, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1240 p hg
    simpa only [d73, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d73, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1286 p hg
    simpa only [d73, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1288 (p : Pattern) (guard : d985 p = 1) : d74 p ≤ (0 : Int) + d1019 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d74, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1241 p hg
    simpa only [d74, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d74, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1287 p hg
    simpa only [d74, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1289 (p : Pattern) (guard : d985 p = 1) : d75 p ≤ (0 : Int) + d1020 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d75, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d75, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d75, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1284 p hg
    simpa only [d75, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1290 (p : Pattern) (guard : d985 p = 1) : d76 p ≤ (0 : Int) + d1021 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d76, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1240 p hg
    simpa only [d76, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d76, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1289 p hg
    simpa only [d76, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1291 (p : Pattern) (guard : d985 p = 1) : d77 p ≤ (0 : Int) + d1022 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d77, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1241 p hg
    simpa only [d77, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d77, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1290 p hg
    simpa only [d77, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1292 (p : Pattern) (guard : d985 p = 1) : d78 p ≤ (0 : Int) + d1023 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d78, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1288 p hg
    simpa only [d78, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d78, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1291 p hg
    simpa only [d78, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1293 (p : Pattern) (guard : d985 p = 1) : d79 p ≤ (0 : Int) + d1024 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d79, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1260 p hg
    simpa only [d79, d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d79, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1289 p hg
    simpa only [d79, d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1294 (p : Pattern) (guard : d985 p = 1) : d80 p ≤ (0 : Int) + d1025 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d80, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1261 p hg
    simpa only [d80, d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d80, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1293 p hg
    simpa only [d80, d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1295 (p : Pattern) (guard : d985 p = 1) : d81 p ≤ (0 : Int) + d1026 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d81, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1270 p hg
    simpa only [d81, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d81, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1289 p hg
    simpa only [d81, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1296 (p : Pattern) (guard : d985 p = 1) : d82 p ≤ (0 : Int) + d1027 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d82, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1271 p hg
    simpa only [d82, d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d82, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1295 p hg
    simpa only [d82, d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1297 (p : Pattern) (guard : d985 p = 1) : d83 p ≤ (0 : Int) + d1028 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d83, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1294 p hg
    simpa only [d83, d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d83, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1296 p hg
    simpa only [d83, d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1298 (p : Pattern) (guard : d985 p = 1) : d84 p ≤ (0 : Int) + d1029 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d84, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1292 p hg
    simpa only [d84, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d84, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1297 p hg
    simpa only [d84, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1299 (p : Pattern) (guard : d985 p = 1) : d85 p ≤ (0 : Int) + d1030 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d85, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1281 p hg
    simpa only [d85, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d85, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1298 p hg
    simpa only [d85, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1300 (p : Pattern) (guard : d985 p = 1) : d86 p ≤ (0 : Int) + d719 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1220 p hg
    simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1266 p hg
    simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1301 (p : Pattern) (guard : d985 p = 1) : d87 p ≤ (0 : Int) + d1031 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d87, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1233 p hg
    simpa only [d87, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d87, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1268 p hg
    simpa only [d87, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1302 (p : Pattern) (guard : d985 p = 1) : d88 p ≤ (0 : Int) + d1032 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d88, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1300 p hg
    simpa only [d88, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d88, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1301 p hg
    simpa only [d88, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1303 (p : Pattern) (guard : d985 p = 1) : d89 p ≤ (0 : Int) + d1033 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d89, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1300 p hg
    simpa only [d89, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d89, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1302 p hg
    simpa only [d89, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1304 (p : Pattern) (guard : d985 p = 1) : d90 p ≤ (0 : Int) + d1034 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d90, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d90, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d90, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1272 p hg
    simpa only [d90, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1305 (p : Pattern) (guard : d985 p = 1) : d91 p ≤ (0 : Int) + d1035 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d91, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1300 p hg
    simpa only [d91, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d91, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1304 p hg
    simpa only [d91, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1306 (p : Pattern) (guard : d985 p = 1) : d92 p ≤ (0 : Int) + d719 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d92, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1252 p hg
    simpa only [d92, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d92, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1275 p hg
    simpa only [d92, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1307 (p : Pattern) (guard : d985 p = 1) : d93 p ≤ (0 : Int) + d1032 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d93, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1306 p hg
    simpa only [d93, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d93, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1301 p hg
    simpa only [d93, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1308 (p : Pattern) (guard : d985 p = 1) : d94 p ≤ (0 : Int) + d1036 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d94, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1305 p hg
    simpa only [d94, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d94, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1307 p hg
    simpa only [d94, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1309 (p : Pattern) (guard : d985 p = 1) : d95 p ≤ (0 : Int) + d1037 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d95, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1303 p hg
    simpa only [d95, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d95, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1308 p hg
    simpa only [d95, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1310 (p : Pattern) (guard : d985 p = 1) : d96 p ≤ (0 : Int) + d1038 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d96, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1259 p hg
    simpa only [d96, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d96, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1309 p hg
    simpa only [d96, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1311 (p : Pattern) (guard : d985 p = 1) : d97 p ≤ (0 : Int) + d705 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1227 p hg
    simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1312 (p : Pattern) (guard : d985 p = 1) : d98 p ≤ (0 : Int) + d706 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1227 p hg
    simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1311 p hg
    simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1313 (p : Pattern) (guard : d985 p = 1) : d99 p ≤ (0 : Int) + d1017 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d99, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1312 p hg
    simpa only [d99, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d99, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1285 p hg
    simpa only [d99, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1314 (p : Pattern) (guard : d985 p = 1) : d100 p ≤ (0 : Int) + d1039 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d100, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1312 p hg
    simpa only [d100, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d100, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1313 p hg
    simpa only [d100, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1315 (p : Pattern) (guard : d985 p = 1) : d101 p ≤ (0 : Int) + d1017 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1313 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1286 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1316 (p : Pattern) (guard : d985 p = 1) : d102 p ≤ (0 : Int) + d1040 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d102, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1314 p hg
    simpa only [d102, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d102, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1315 p hg
    simpa only [d102, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1317 (p : Pattern) (guard : d985 p = 1) : d103 p ≤ (0 : Int) + d1041 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d103, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d103, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d103, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1316 p hg
    simpa only [d103, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1318 (p : Pattern) (guard : d985 p = 1) : d104 p ≤ (0 : Int) + d1042 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d104, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1302 p hg
    simpa only [d104, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d104, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1289 p hg
    simpa only [d104, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1319 (p : Pattern) (guard : d985 p = 1) : d105 p ≤ (0 : Int) + d1043 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d105, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1303 p hg
    simpa only [d105, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d105, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1318 p hg
    simpa only [d105, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1320 (p : Pattern) (guard : d985 p = 1) : d106 p ≤ (0 : Int) + d1044 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d106, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1291 p hg
    simpa only [d106, d1044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d106, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1319 p hg
    simpa only [d106, d1044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1321 (p : Pattern) (guard : d985 p = 1) : d107 p ≤ (0 : Int) + d1045 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d107, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1313 p hg
    simpa only [d107, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d107, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d107, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1322 (p : Pattern) (guard : d985 p = 1) : d108 p ≤ (0 : Int) + d1046 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d108, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1314 p hg
    simpa only [d108, d1046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d108, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1321 p hg
    simpa only [d108, d1046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1323 (p : Pattern) (guard : d985 p = 1) : d109 p ≤ (0 : Int) + d1020 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d109, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1311 p hg
    simpa only [d109, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d109, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1284 p hg
    simpa only [d109, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1324 (p : Pattern) (guard : d985 p = 1) : d110 p ≤ (0 : Int) + d1047 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d110, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1311 p hg
    simpa only [d110, d1047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d110, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d110, d1047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1325 (p : Pattern) (guard : d985 p = 1) : d111 p ≤ (0 : Int) + d1048 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d111, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d111, d1048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d111, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d111, d1048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1326 (p : Pattern) (guard : d985 p = 1) : d112 p ≤ (0 : Int) + d1049 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d112, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1324 p hg
    simpa only [d112, d1049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d112, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1325 p hg
    simpa only [d112, d1049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1327 (p : Pattern) (guard : d985 p = 1) : d113 p ≤ (0 : Int) + d1050 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d113, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1322 p hg
    simpa only [d113, d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d113, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1326 p hg
    simpa only [d113, d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1328 (p : Pattern) (guard : d985 p = 1) : d114 p ≤ (0 : Int) + d1051 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d114, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1320 p hg
    simpa only [d114, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d114, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1327 p hg
    simpa only [d114, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1329 (p : Pattern) (guard : d985 p = 1) : d115 p ≤ (0 : Int) + d1052 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d115, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1317 p hg
    simpa only [d115, d1052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d115, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1328 p hg
    simpa only [d115, d1052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1330 (p : Pattern) (guard : d985 p = 1) : d116 p ≤ (0 : Int) + d1053 p := by
  cases selected : p 86 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d116, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1299 p hg
    simpa only [d116, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d116, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1329 p hg
    simpa only [d116, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1331 (p : Pattern) (guard : d985 p = 1) : d117 p ≤ (0 : Int) + d1054 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d117, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1291 p hg
    simpa only [d117, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d117, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1297 p hg
    simpa only [d117, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1332 (p : Pattern) (guard : d985 p = 1) : d118 p ≤ (0 : Int) + d1055 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d118, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1281 p hg
    simpa only [d118, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d118, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1331 p hg
    simpa only [d118, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1333 (p : Pattern) (guard : d985 p = 1) : d119 p ≤ (0 : Int) + d1056 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d119, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d119, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d119, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1233 p hg
    simpa only [d119, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1334 (p : Pattern) (guard : d985 p = 1) : d120 p ≤ (0 : Int) + d1057 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d120, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1333 p hg
    simpa only [d120, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d120, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1272 p hg
    simpa only [d120, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1335 (p : Pattern) (guard : d985 p = 1) : d121 p ≤ (0 : Int) + d1058 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d121, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1300 p hg
    simpa only [d121, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d121, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1334 p hg
    simpa only [d121, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1336 (p : Pattern) (guard : d985 p = 1) : d122 p ≤ (0 : Int) + d1059 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d122, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1335 p hg
    simpa only [d122, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d122, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1307 p hg
    simpa only [d122, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1337 (p : Pattern) (guard : d985 p = 1) : d123 p ≤ (0 : Int) + d1060 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d123, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1303 p hg
    simpa only [d123, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d123, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1336 p hg
    simpa only [d123, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1338 (p : Pattern) (guard : d985 p = 1) : d124 p ≤ (0 : Int) + d1061 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d124, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1259 p hg
    simpa only [d124, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d124, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1337 p hg
    simpa only [d124, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1339 (p : Pattern) (guard : d985 p = 1) : d125 p ≤ (0 : Int) + d1020 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1289 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1340 (p : Pattern) (guard : d985 p = 1) : d126 p ≤ (0 : Int) + d1062 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d126, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1324 p hg
    simpa only [d126, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d126, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1339 p hg
    simpa only [d126, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1341 (p : Pattern) (guard : d985 p = 1) : d127 p ≤ (0 : Int) + d1063 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d127, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1316 p hg
    simpa only [d127, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d127, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1340 p hg
    simpa only [d127, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1342 (p : Pattern) (guard : d985 p = 1) : d128 p ≤ (0 : Int) + d1064 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d128, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1338 p hg
    simpa only [d128, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d128, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1341 p hg
    simpa only [d128, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1343 (p : Pattern) (guard : d985 p = 1) : d129 p ≤ (0 : Int) + d1065 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d129, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1291 p hg
    simpa only [d129, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d129, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1296 p hg
    simpa only [d129, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1344 (p : Pattern) (guard : d985 p = 1) : d130 p ≤ (0 : Int) + d1066 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d130, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1326 p hg
    simpa only [d130, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d130, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d130, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1345 (p : Pattern) (guard : d985 p = 1) : d131 p ≤ (0 : Int) + d1067 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d131, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1343 p hg
    simpa only [d131, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d131, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1344 p hg
    simpa only [d131, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1346 (p : Pattern) (guard : d985 p = 1) : d132 p ≤ (0 : Int) + d1068 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d132, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1342 p hg
    simpa only [d132, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d132, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1345 p hg
    simpa only [d132, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1347 (p : Pattern) (guard : d985 p = 1) : d133 p ≤ (0 : Int) + d1069 p := by
  cases selected : p 86 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d133, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1332 p hg
    simpa only [d133, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d133, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1346 p hg
    simpa only [d133, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1348 (p : Pattern) (guard : d985 p = 1) : d134 p ≤ (0 : Int) + d1070 p := by
  cases selected : p 80 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d134, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1330 p hg
    simpa only [d134, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d134, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1347 p hg
    simpa only [d134, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1349 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1350 (p : Pattern) (guard : d835 p = 1) : d184 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d184, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d835, d184, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d184, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1349 p hg
    simpa only [d835, d184, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1351 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d83 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1352 (p : Pattern) (guard : d835 p = 1) : d185 p ≤ (0 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d185, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare421 p hg
    simpa only [d835, d185, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d185, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1351 p hg
    simpa only [d835, d185, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1353 (p : Pattern) (guard : d835 p = 1) : d186 p ≤ (0 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d835 p = 1 := by simpa only [d186, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1350 p hg
    simpa only [d186, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d186, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1352 p hg
    simpa only [d186, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1354 (p : Pattern) (guard : d0 p = 1) : d206 p ≤ (0 : Int) + d166 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1355 (p : Pattern) (guard : d854 p = 1) : d207 p ≤ (0 : Int) + d174 p := by
  cases selected : p 86 with
  | false =>
    have hg : d835 p = 1 := by simpa only [d854, d207, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1353 p hg
    simpa only [d854, d207, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d207, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1354 p hg
    simpa only [d854, d207, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1356 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1357 (p : Pattern) (guard : d835 p = 1) : d208 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d208, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare418 p hg
    simpa only [d835, d208, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d208, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1356 p hg
    simpa only [d835, d208, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1358 (p : Pattern) (guard : d0 p = 1) : d164 p ≤ (0 : Int) + d83 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1359 (p : Pattern) (guard : d835 p = 1) : d209 p ≤ (0 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d835, d209, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare429 p hg
    simpa only [d835, d209, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d209, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1358 p hg
    simpa only [d835, d209, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1360 (p : Pattern) (guard : d835 p = 1) : d210 p ≤ (0 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d835 p = 1 := by simpa only [d210, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1357 p hg
    simpa only [d210, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d210, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1359 p hg
    simpa only [d210, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1361 (p : Pattern) (guard : d0 p = 1) : d225 p ≤ (0 : Int) + d171 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1362 (p : Pattern) (guard : d854 p = 1) : d226 p ≤ (0 : Int) + d175 p := by
  cases selected : p 86 with
  | false =>
    have hg : d835 p = 1 := by simpa only [d854, d226, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1360 p hg
    simpa only [d854, d226, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d226, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1361 p hg
    simpa only [d854, d226, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1363 (p : Pattern) (guard : d854 p = 1) : d227 p ≤ (0 : Int) + d176 p := by
  cases selected : p 80 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d227, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1355 p hg
    simpa only [d227, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d227, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1362 p hg
    simpa only [d227, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1364 (p : Pattern) (guard : d0 p = 1) : d186 p ≤ (1 : Int) + d85 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1365 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (1 : Int) + d0 p := by
  change (1 : Int) ≤ (1 : Int) + 0
  decide
theorem compare1366 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (1 : Int) + d3 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1365 p hg
    simpa only [d9, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d9, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1367 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (1 : Int) + d4 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1365 p hg
    simpa only [d10, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1366 p hg
    simpa only [d10, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1368 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (1 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d11, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1365 p hg
    simpa only [d11, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d11, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d11, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1369 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d12, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1367 p hg
    simpa only [d12, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d12, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1368 p hg
    simpa only [d12, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1370 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (1 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1367 p hg
    simpa only [d13, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d13, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1371 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (1 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1369 p hg
    simpa only [d14, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1370 p hg
    simpa only [d14, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1372 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (1 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1371 p hg
    simpa only [d97, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare387 p hg
    simpa only [d97, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1373 (p : Pattern) (guard : d1 p = 1) : d187 p ≤ (1 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d187, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d187, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d187, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1372 p hg
    simpa only [d187, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1374 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (1 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1366 p hg
    simpa only [d21, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d21, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1375 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (1 : Int) + d18 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1367 p hg
    simpa only [d22, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1374 p hg
    simpa only [d22, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1376 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (1 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1374 p hg
    simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d23, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1377 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (1 : Int) + d20 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1375 p hg
    simpa only [d24, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1376 p hg
    simpa only [d24, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1378 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (1 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1377 p hg
    simpa only [d70, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare393 p hg
    simpa only [d70, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1379 (p : Pattern) (guard : d1 p = 1) : d188 p ≤ (1 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d188, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare75 p hg
    simpa only [d188, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d188, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1378 p hg
    simpa only [d188, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1380 (p : Pattern) (guard : d1 p = 1) : d189 p ≤ (1 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d189, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1373 p hg
    simpa only [d189, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d189, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1379 p hg
    simpa only [d189, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1381 (p : Pattern) (guard : d1 p = 1) : d190 p ≤ (1 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1373 p hg
    simpa only [d190, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1380 p hg
    simpa only [d190, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1382 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (1 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1365 p hg
    simpa only [d9, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare381 p hg
    simpa only [d9, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1383 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (1 : Int) + d30 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1382 p hg
    simpa only [d21, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d21, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1384 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (1 : Int) + d31 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1367 p hg
    simpa only [d22, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1383 p hg
    simpa only [d22, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1385 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (1 : Int) + d32 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1383 p hg
    simpa only [d23, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d23, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1386 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (1 : Int) + d33 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1384 p hg
    simpa only [d24, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1385 p hg
    simpa only [d24, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1387 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (1 : Int) + d34 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1386 p hg
    simpa only [d70, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare393 p hg
    simpa only [d70, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1388 (p : Pattern) (guard : d1 p = 1) : d191 p ≤ (1 : Int) + d35 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d191, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35 p hg
    simpa only [d191, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d191, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1387 p hg
    simpa only [d191, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1389 (p : Pattern) (guard : d1 p = 1) : d192 p ≤ (1 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d192, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1373 p hg
    simpa only [d192, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d192, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1388 p hg
    simpa only [d192, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1390 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (1 : Int) + d38 p := by
  omega
theorem compare1391 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (1 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1368 p hg
    simpa only [d39, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d39, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1392 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (1 : Int) + d38 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1369 p hg
    simpa only [d40, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1391 p hg
    simpa only [d40, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1393 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (1 : Int) + d41 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1392 p hg
    simpa only [d68, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare398 p hg
    simpa only [d68, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1394 (p : Pattern) (guard : d1 p = 1) : d193 p ≤ (1 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d193, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1390 p hg
    simpa only [d193, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d193, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1393 p hg
    simpa only [d193, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1395 (p : Pattern) (guard : d1 p = 1) : d194 p ≤ (1 : Int) + d43 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d194, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1394 p hg
    simpa only [d194, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d194, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1379 p hg
    simpa only [d194, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1396 (p : Pattern) (guard : d1 p = 1) : d195 p ≤ (1 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d195, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1389 p hg
    simpa only [d195, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d195, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1395 p hg
    simpa only [d195, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1397 (p : Pattern) (guard : d1 p = 1) : d196 p ≤ (1 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d196, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1381 p hg
    simpa only [d196, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d196, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d196, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1398 (p : Pattern) (guard : d1 p = 1) : d197 p ≤ (1 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1397 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1399 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (1 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban32Refined
