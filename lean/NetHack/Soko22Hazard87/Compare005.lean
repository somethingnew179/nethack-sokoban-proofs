import NetHack.Soko22Hazard87.Compare004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1250 (p : Pattern) (guard : d17603 p = 1) : d47807 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17602 p = 1 := by simpa only [d17603, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1249 p hg
    simpa only [d17603, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17603, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1185 p hg
    simpa only [d17603, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1251 (p : Pattern) (guard : d17604 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17604, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d17604, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17603 p = 1 := by simpa only [d17604, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1250 p hg
    simpa only [d17604, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1252 (p : Pattern) (guard : d17605 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17604 p = 1 := by simpa only [d17605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1251 p hg
    simpa only [d17605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17572 p = 1 := by simpa only [d17605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1187 p hg
    simpa only [d17605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1253 (p : Pattern) (guard : d17606 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17605 p = 1 := by simpa only [d17606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1252 p hg
    simpa only [d17606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1254 (p : Pattern) (guard : d17607 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17606 p = 1 := by simpa only [d17607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1253 p hg
    simpa only [d17607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1255 (p : Pattern) (guard : d17608 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17607 p = 1 := by simpa only [d17608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d17608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1256 (p : Pattern) (guard : d17609 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17608 p = 1 := by simpa only [d17609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1255 p hg
    simpa only [d17609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17576 p = 1 := by simpa only [d17609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1191 p hg
    simpa only [d17609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1257 (p : Pattern) (guard : d61089 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17609 p = 1 := by simpa only [d61089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1256 p hg
    simpa only [d61089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1258 (p : Pattern) (guard : d61090 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d61089 p = 1 := by simpa only [d61090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1257 p hg
    simpa only [d61090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1259 (p : Pattern) (guard : d61091 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61090 p = 1 := by simpa only [d61091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1258 p hg
    simpa only [d61091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1260 (p : Pattern) (guard : d61092 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61091 p = 1 := by simpa only [d61092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1259 p hg
    simpa only [d61092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1261 (p : Pattern) (guard : d61093 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61093, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d61093, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61092 p = 1 := by simpa only [d61093, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1260 p hg
    simpa only [d61093, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1262 (p : Pattern) (guard : d61094 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61093 p = 1 := by simpa only [d61094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1261 p hg
    simpa only [d61094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1263 (p : Pattern) (guard : d61095 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d61094 p = 1 := by simpa only [d61095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1262 p hg
    simpa only [d61095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1264 (p : Pattern) (guard : d61096 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d61095 p = 1 := by simpa only [d61096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1263 p hg
    simpa only [d61096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1265 (p : Pattern) (guard : d61097 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d61096 p = 1 := by simpa only [d61097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1264 p hg
    simpa only [d61097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1266 (p : Pattern) (guard : d61098 p = 1) : d47865 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d61097 p = 1 := by simpa only [d61098, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1265 p hg
    simpa only [d61098, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61098, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1202 p hg
    simpa only [d61098, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1267 (p : Pattern) (guard : d61099 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61099, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1129 p hg
    simpa only [d61099, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61098 p = 1 := by simpa only [d61099, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1266 p hg
    simpa only [d61099, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1268 (p : Pattern) (guard : d61100 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61099 p = 1 := by simpa only [d61100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1267 p hg
    simpa only [d61100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1269 (p : Pattern) (guard : d61101 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61100 p = 1 := by simpa only [d61101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1268 p hg
    simpa only [d61101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1270 (p : Pattern) (guard : d61102 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61101 p = 1 := by simpa only [d61102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1269 p hg
    simpa only [d61102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1271 (p : Pattern) (guard : d61103 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61102 p = 1 := by simpa only [d61103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1270 p hg
    simpa only [d61103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1272 (p : Pattern) (guard : d61104 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61103 p = 1 := by simpa only [d61104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1271 p hg
    simpa only [d61104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1273 (p : Pattern) (guard : d61105 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d61088 p = 1 := by simpa only [d61105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1209 p hg
    simpa only [d61105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61104 p = 1 := by simpa only [d61105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1272 p hg
    simpa only [d61105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1274 (p : Pattern) (guard : d307 p = 1) : d2 p ≤ (-1 : Int) + d3 p := by
  have ha := bounds2 p
  have hb := bounds3 p
  omega
theorem compare1275 (p : Pattern) (guard : d127 p = 1) : d2 p ≤ (-1 : Int) + d3 p := by
  have ha := bounds2 p
  have hb := bounds3 p
  omega
theorem compare1276 (p : Pattern) (guard : d308 p = 1) : d47629 p ≤ (-1 : Int) + d47714 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1275 p hg
    simpa only [d308, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d308, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1277 (p : Pattern) (guard : d309 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d309, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1276 p hg
    simpa only [d309, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1278 (p : Pattern) (guard : d310 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1214 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1279 (p : Pattern) (guard : d311 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1278 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1215 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1280 (p : Pattern) (guard : d312 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1279 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1216 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1281 (p : Pattern) (guard : d313 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1280 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1282 (p : Pattern) (guard : d314 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1281 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1283 (p : Pattern) (guard : d315 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1219 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1284 (p : Pattern) (guard : d316 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1283 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1220 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1285 (p : Pattern) (guard : d317 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1284 p hg
    simpa only [d317, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d317, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1286 (p : Pattern) (guard : d318 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1285 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1222 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1287 (p : Pattern) (guard : d412 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d412, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d412, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318 p = 1 := by simpa only [d412, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1286 p hg
    simpa only [d412, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1288 (p : Pattern) (guard : d307 p = 1) : d4 p ≤ (-1 : Int) + d5 p := by
  have ha := bounds4 p
  have hb := bounds5 p
  omega
theorem compare1289 (p : Pattern) (guard : d127 p = 1) : d4 p ≤ (-1 : Int) + d5 p := by
  have ha := bounds4 p
  have hb := bounds5 p
  omega
theorem compare1290 (p : Pattern) (guard : d308 p = 1) : d47616 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1289 p hg
    simpa only [d308, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d308, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1291 (p : Pattern) (guard : d309 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1288 p hg
    simpa only [d309, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1290 p hg
    simpa only [d309, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1292 (p : Pattern) (guard : d310 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1291 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1228 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1293 (p : Pattern) (guard : d311 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1292 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1229 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1294 (p : Pattern) (guard : d312 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1293 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1230 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1295 (p : Pattern) (guard : d313 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1294 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1296 (p : Pattern) (guard : d314 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1295 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1297 (p : Pattern) (guard : d315 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1296 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1233 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1298 (p : Pattern) (guard : d316 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1297 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1234 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1299 (p : Pattern) (guard : d317 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1298 p hg
    simpa only [d317, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d317, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1300 (p : Pattern) (guard : d318 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1299 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1236 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1301 (p : Pattern) (guard : d319 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1300 p hg
    simpa only [d319, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d319, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1302 (p : Pattern) (guard : d413 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d412 p = 1 := by simpa only [d413, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1287 p hg
    simpa only [d413, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d319 p = 1 := by simpa only [d413, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1301 p hg
    simpa only [d413, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1303 (p : Pattern) (guard : d17643 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d413 p = 1 := by simpa only [d17643, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1302 p hg
    simpa only [d17643, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17643, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d17643, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1304 (p : Pattern) (guard : d17644 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17643 p = 1 := by simpa only [d17644, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1303 p hg
    simpa only [d17644, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17644, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d17644, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1305 (p : Pattern) (guard : d17645 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17644 p = 1 := by simpa only [d17645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1304 p hg
    simpa only [d17645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17594 p = 1 := by simpa only [d17645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1241 p hg
    simpa only [d17645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1306 (p : Pattern) (guard : d60575 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17645 p = 1 := by simpa only [d60575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1305 p hg
    simpa only [d60575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17595 p = 1 := by simpa only [d60575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d60575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1307 (p : Pattern) (guard : d60576 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60575 p = 1 := by simpa only [d60576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1306 p hg
    simpa only [d60576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17596 p = 1 := by simpa only [d60576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1243 p hg
    simpa only [d60576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1308 (p : Pattern) (guard : d60577 p = 1) : d47804 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60577, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1135 p hg
    simpa only [d60577, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60576 p = 1 := by simpa only [d60577, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1307 p hg
    simpa only [d60577, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1309 (p : Pattern) (guard : d60578 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60578, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1134 p hg
    simpa only [d60578, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60577 p = 1 := by simpa only [d60578, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1308 p hg
    simpa only [d60578, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1310 (p : Pattern) (guard : d60579 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60578 p = 1 := by simpa only [d60579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1309 p hg
    simpa only [d60579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17599 p = 1 := by simpa only [d60579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d60579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1311 (p : Pattern) (guard : d17730 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17599 p = 1 := by simpa only [d17730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d17730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d17730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1312 (p : Pattern) (guard : d60618 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60579 p = 1 := by simpa only [d60618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d60618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17730 p = 1 := by simpa only [d60618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1311 p hg
    simpa only [d60618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1313 (p : Pattern) (guard : d60619 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60618 p = 1 := by simpa only [d60619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1312 p hg
    simpa only [d60619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d60619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1314 (p : Pattern) (guard : d60620 p = 1) : d47807 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60619 p = 1 := by simpa only [d60620, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1313 p hg
    simpa only [d60620, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60620, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1185 p hg
    simpa only [d60620, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1315 (p : Pattern) (guard : d60621 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60621, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d60621, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60620 p = 1 := by simpa only [d60621, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1314 p hg
    simpa only [d60621, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1316 (p : Pattern) (guard : d17739 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17730 p = 1 := by simpa only [d17739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1311 p hg
    simpa only [d17739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d17739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1317 (p : Pattern) (guard : d17740 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17739 p = 1 := by simpa only [d17740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1316 p hg
    simpa only [d17740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d17740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1318 (p : Pattern) (guard : d17741 p = 1) : d47807 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17740 p = 1 := by simpa only [d17741, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1317 p hg
    simpa only [d17741, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17741, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1185 p hg
    simpa only [d17741, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1319 (p : Pattern) (guard : d17742 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17742, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d17742, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17741 p = 1 := by simpa only [d17742, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1318 p hg
    simpa only [d17742, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1320 (p : Pattern) (guard : d60626 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60621 p = 1 := by simpa only [d60626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1315 p hg
    simpa only [d60626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17742 p = 1 := by simpa only [d60626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1319 p hg
    simpa only [d60626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1321 (p : Pattern) (guard : d60627 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60626 p = 1 := by simpa only [d60627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1320 p hg
    simpa only [d60627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1322 (p : Pattern) (guard : d60628 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60627 p = 1 := by simpa only [d60628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1321 p hg
    simpa only [d60628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1323 (p : Pattern) (guard : d60629 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60628 p = 1 := by simpa only [d60629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1322 p hg
    simpa only [d60629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1324 (p : Pattern) (guard : d17789 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17742 p = 1 := by simpa only [d17789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1319 p hg
    simpa only [d17789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1325 (p : Pattern) (guard : d17790 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17789 p = 1 := by simpa only [d17790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1324 p hg
    simpa only [d17790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1326 (p : Pattern) (guard : d17791 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17790 p = 1 := by simpa only [d17791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1325 p hg
    simpa only [d17791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1327 (p : Pattern) (guard : d17792 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17791 p = 1 := by simpa only [d17792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1326 p hg
    simpa only [d17792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1328 (p : Pattern) (guard : d61106 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60629 p = 1 := by simpa only [d61106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d61106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17792 p = 1 := by simpa only [d61106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1327 p hg
    simpa only [d61106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1329 (p : Pattern) (guard : d61107 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61106 p = 1 := by simpa only [d61107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1328 p hg
    simpa only [d61107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1330 (p : Pattern) (guard : d61108 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d61107 p = 1 := by simpa only [d61108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1329 p hg
    simpa only [d61108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1331 (p : Pattern) (guard : d61109 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61108 p = 1 := by simpa only [d61109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1330 p hg
    simpa only [d61109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1332 (p : Pattern) (guard : d61110 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61109 p = 1 := by simpa only [d61110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1331 p hg
    simpa only [d61110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1333 (p : Pattern) (guard : d61111 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61111, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d61111, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61110 p = 1 := by simpa only [d61111, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1332 p hg
    simpa only [d61111, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1334 (p : Pattern) (guard : d61112 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61111 p = 1 := by simpa only [d61112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1333 p hg
    simpa only [d61112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1335 (p : Pattern) (guard : d61113 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d61112 p = 1 := by simpa only [d61113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1334 p hg
    simpa only [d61113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1336 (p : Pattern) (guard : d61114 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d61113 p = 1 := by simpa only [d61114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1335 p hg
    simpa only [d61114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1337 (p : Pattern) (guard : d61115 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d61114 p = 1 := by simpa only [d61115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1336 p hg
    simpa only [d61115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1338 (p : Pattern) (guard : d61116 p = 1) : d47865 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d61115 p = 1 := by simpa only [d61116, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1337 p hg
    simpa only [d61116, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61116, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1202 p hg
    simpa only [d61116, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1339 (p : Pattern) (guard : d61117 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61117, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1129 p hg
    simpa only [d61117, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61116 p = 1 := by simpa only [d61117, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1338 p hg
    simpa only [d61117, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1340 (p : Pattern) (guard : d61118 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61117 p = 1 := by simpa only [d61118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1339 p hg
    simpa only [d61118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1341 (p : Pattern) (guard : d61119 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61118 p = 1 := by simpa only [d61119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1340 p hg
    simpa only [d61119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1342 (p : Pattern) (guard : d61120 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61119 p = 1 := by simpa only [d61120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1341 p hg
    simpa only [d61120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1343 (p : Pattern) (guard : d61121 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61120 p = 1 := by simpa only [d61121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1342 p hg
    simpa only [d61121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1344 (p : Pattern) (guard : d61122 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61121 p = 1 := by simpa only [d61122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1343 p hg
    simpa only [d61122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1345 (p : Pattern) (guard : d61123 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61122 p = 1 := by simpa only [d61123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1344 p hg
    simpa only [d61123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1346 (p : Pattern) (guard : d61124 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d61105 p = 1 := by simpa only [d61124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1273 p hg
    simpa only [d61124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61123 p = 1 := by simpa only [d61124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1345 p hg
    simpa only [d61124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1347 (p : Pattern) (guard : d528 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1348 (p : Pattern) (guard : d529 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1347 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1278 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1349 (p : Pattern) (guard : d530 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1348 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1279 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1350 (p : Pattern) (guard : d531 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1349 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1351 (p : Pattern) (guard : d532 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1350 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1352 (p : Pattern) (guard : d533 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1351 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1353 (p : Pattern) (guard : d534 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1214 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1354 (p : Pattern) (guard : d535 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1278 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1353 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1355 (p : Pattern) (guard : d536 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1354 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1216 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1356 (p : Pattern) (guard : d537 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1355 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1357 (p : Pattern) (guard : d538 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1356 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1358 (p : Pattern) (guard : d539 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1357 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1219 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1359 (p : Pattern) (guard : d540 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1352 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1358 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1360 (p : Pattern) (guard : d541 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1359 p hg
    simpa only [d541, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d541, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1361 (p : Pattern) (guard : d542 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1360 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1285 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1362 (p : Pattern) (guard : d659 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d659, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d659, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d542 p = 1 := by simpa only [d659, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1361 p hg
    simpa only [d659, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1363 (p : Pattern) (guard : d528 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1291 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1364 (p : Pattern) (guard : d529 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1363 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1292 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1365 (p : Pattern) (guard : d530 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1364 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1293 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1366 (p : Pattern) (guard : d531 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1365 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1367 (p : Pattern) (guard : d532 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1366 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1368 (p : Pattern) (guard : d533 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1367 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1296 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1369 (p : Pattern) (guard : d534 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1228 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1370 (p : Pattern) (guard : d535 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1292 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1369 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1371 (p : Pattern) (guard : d536 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1370 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1230 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1372 (p : Pattern) (guard : d537 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1371 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1373 (p : Pattern) (guard : d538 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1372 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1374 (p : Pattern) (guard : d539 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1373 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1233 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1375 (p : Pattern) (guard : d540 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1368 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1374 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1376 (p : Pattern) (guard : d541 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1375 p hg
    simpa only [d541, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d541, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1377 (p : Pattern) (guard : d542 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1376 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1299 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1378 (p : Pattern) (guard : d543 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1377 p hg
    simpa only [d543, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d543, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1379 (p : Pattern) (guard : d660 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d659 p = 1 := by simpa only [d660, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1362 p hg
    simpa only [d660, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d543 p = 1 := by simpa only [d660, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1378 p hg
    simpa only [d660, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1380 (p : Pattern) (guard : d17709 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d660 p = 1 := by simpa only [d17709, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1379 p hg
    simpa only [d17709, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17709, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d17709, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1381 (p : Pattern) (guard : d17710 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17709 p = 1 := by simpa only [d17710, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1380 p hg
    simpa only [d17710, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17710, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d17710, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1382 (p : Pattern) (guard : d60608 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17710 p = 1 := by simpa only [d60608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1381 p hg
    simpa only [d60608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17644 p = 1 := by simpa only [d60608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1304 p hg
    simpa only [d60608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1383 (p : Pattern) (guard : d750 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1222 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1150 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1384 (p : Pattern) (guard : d971 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d971, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d971, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d750 p = 1 := by simpa only [d971, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1383 p hg
    simpa only [d971, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1385 (p : Pattern) (guard : d750 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1236 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1166 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1386 (p : Pattern) (guard : d751 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1385 p hg
    simpa only [d751, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d751, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1387 (p : Pattern) (guard : d972 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d971 p = 1 := by simpa only [d972, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1384 p hg
    simpa only [d972, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d751 p = 1 := by simpa only [d972, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1386 p hg
    simpa only [d972, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1388 (p : Pattern) (guard : d17821 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d972 p = 1 := by simpa only [d17821, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1387 p hg
    simpa only [d17821, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17821, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d17821, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1389 (p : Pattern) (guard : d17822 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17821 p = 1 := by simpa only [d17822, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1388 p hg
    simpa only [d17822, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17822, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d17822, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1390 (p : Pattern) (guard : d17834 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17644 p = 1 := by simpa only [d17834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1304 p hg
    simpa only [d17834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17822 p = 1 := by simpa only [d17834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1389 p hg
    simpa only [d17834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1391 (p : Pattern) (guard : d60653 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60608 p = 1 := by simpa only [d60653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1382 p hg
    simpa only [d60653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17834 p = 1 := by simpa only [d60653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1390 p hg
    simpa only [d60653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1392 (p : Pattern) (guard : d17828 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17822 p = 1 := by simpa only [d17828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1389 p hg
    simpa only [d17828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1175 p hg
    simpa only [d17828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1393 (p : Pattern) (guard : d17835 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17834 p = 1 := by simpa only [d17835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1390 p hg
    simpa only [d17835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17828 p = 1 := by simpa only [d17835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1392 p hg
    simpa only [d17835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1394 (p : Pattern) (guard : d60657 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60653 p = 1 := by simpa only [d60657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1391 p hg
    simpa only [d60657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17835 p = 1 := by simpa only [d60657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1393 p hg
    simpa only [d60657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1395 (p : Pattern) (guard : d60658 p = 1) : d47804 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60658, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1135 p hg
    simpa only [d60658, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60657 p = 1 := by simpa only [d60658, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1394 p hg
    simpa only [d60658, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1396 (p : Pattern) (guard : d60659 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60659, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1134 p hg
    simpa only [d60659, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60658 p = 1 := by simpa only [d60659, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1395 p hg
    simpa only [d60659, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1397 (p : Pattern) (guard : d17839 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17828 p = 1 := by simpa only [d17839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1392 p hg
    simpa only [d17839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1175 p hg
    simpa only [d17839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1398 (p : Pattern) (guard : d17840 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17835 p = 1 := by simpa only [d17840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1393 p hg
    simpa only [d17840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17839 p = 1 := by simpa only [d17840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1397 p hg
    simpa only [d17840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1399 (p : Pattern) (guard : d17841 p = 1) : d47804 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17841, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1135 p hg
    simpa only [d17841, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17840 p = 1 := by simpa only [d17841, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1398 p hg
    simpa only [d17841, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1400 (p : Pattern) (guard : d17842 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17842, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1134 p hg
    simpa only [d17842, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17841 p = 1 := by simpa only [d17842, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1399 p hg
    simpa only [d17842, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1401 (p : Pattern) (guard : d60661 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60659 p = 1 := by simpa only [d60661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d60661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17842 p = 1 := by simpa only [d60661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1400 p hg
    simpa only [d60661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1402 (p : Pattern) (guard : d17848 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17842 p = 1 := by simpa only [d17848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1400 p hg
    simpa only [d17848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d17848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1403 (p : Pattern) (guard : d60666 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60661 p = 1 := by simpa only [d60666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1401 p hg
    simpa only [d60666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17848 p = 1 := by simpa only [d60666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1402 p hg
    simpa only [d60666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1404 (p : Pattern) (guard : d60667 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60666 p = 1 := by simpa only [d60667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1403 p hg
    simpa only [d60667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d60667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1405 (p : Pattern) (guard : d60668 p = 1) : d47807 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60667 p = 1 := by simpa only [d60668, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1404 p hg
    simpa only [d60668, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60668, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1185 p hg
    simpa only [d60668, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1406 (p : Pattern) (guard : d60669 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60669, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d60669, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60668 p = 1 := by simpa only [d60669, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1405 p hg
    simpa only [d60669, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1407 (p : Pattern) (guard : d17857 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17848 p = 1 := by simpa only [d17857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1402 p hg
    simpa only [d17857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d17857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1408 (p : Pattern) (guard : d17858 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17857 p = 1 := by simpa only [d17858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1407 p hg
    simpa only [d17858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d17858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1409 (p : Pattern) (guard : d17859 p = 1) : d47807 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17858 p = 1 := by simpa only [d17859, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1408 p hg
    simpa only [d17859, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17859, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1185 p hg
    simpa only [d17859, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1410 (p : Pattern) (guard : d17860 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17860, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d17860, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17859 p = 1 := by simpa only [d17860, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1409 p hg
    simpa only [d17860, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1411 (p : Pattern) (guard : d60674 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60669 p = 1 := by simpa only [d60674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1406 p hg
    simpa only [d60674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17860 p = 1 := by simpa only [d60674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1410 p hg
    simpa only [d60674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1412 (p : Pattern) (guard : d60675 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60674 p = 1 := by simpa only [d60675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d60675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1413 (p : Pattern) (guard : d60676 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60675 p = 1 := by simpa only [d60676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1412 p hg
    simpa only [d60676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1414 (p : Pattern) (guard : d60677 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60676 p = 1 := by simpa only [d60677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1413 p hg
    simpa only [d60677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1415 (p : Pattern) (guard : d17918 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17860 p = 1 := by simpa only [d17918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1410 p hg
    simpa only [d17918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1416 (p : Pattern) (guard : d17919 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17918 p = 1 := by simpa only [d17919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1415 p hg
    simpa only [d17919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1417 (p : Pattern) (guard : d17920 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17919 p = 1 := by simpa only [d17920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1416 p hg
    simpa only [d17920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1418 (p : Pattern) (guard : d17921 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17920 p = 1 := by simpa only [d17921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1417 p hg
    simpa only [d17921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d17921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1419 (p : Pattern) (guard : d61125 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60677 p = 1 := by simpa only [d61125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1414 p hg
    simpa only [d61125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17921 p = 1 := by simpa only [d61125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1418 p hg
    simpa only [d61125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1420 (p : Pattern) (guard : d61126 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61125 p = 1 := by simpa only [d61126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1419 p hg
    simpa only [d61126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1421 (p : Pattern) (guard : d61127 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d61126 p = 1 := by simpa only [d61127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1420 p hg
    simpa only [d61127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1422 (p : Pattern) (guard : d61128 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61127 p = 1 := by simpa only [d61128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1421 p hg
    simpa only [d61128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1423 (p : Pattern) (guard : d61129 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61128 p = 1 := by simpa only [d61129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1422 p hg
    simpa only [d61129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1424 (p : Pattern) (guard : d61130 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61130, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d61130, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61129 p = 1 := by simpa only [d61130, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1423 p hg
    simpa only [d61130, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1425 (p : Pattern) (guard : d61131 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61130 p = 1 := by simpa only [d61131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1424 p hg
    simpa only [d61131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1426 (p : Pattern) (guard : d61132 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d61131 p = 1 := by simpa only [d61132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1425 p hg
    simpa only [d61132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1427 (p : Pattern) (guard : d61133 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d61132 p = 1 := by simpa only [d61133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1426 p hg
    simpa only [d61133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1428 (p : Pattern) (guard : d61134 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d61133 p = 1 := by simpa only [d61134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1427 p hg
    simpa only [d61134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1429 (p : Pattern) (guard : d61135 p = 1) : d47865 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d61134 p = 1 := by simpa only [d61135, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1428 p hg
    simpa only [d61135, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61135, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1202 p hg
    simpa only [d61135, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1430 (p : Pattern) (guard : d61136 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61136, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1129 p hg
    simpa only [d61136, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61135 p = 1 := by simpa only [d61136, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1429 p hg
    simpa only [d61136, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1431 (p : Pattern) (guard : d61137 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61136 p = 1 := by simpa only [d61137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1430 p hg
    simpa only [d61137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1432 (p : Pattern) (guard : d61138 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61137 p = 1 := by simpa only [d61138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1431 p hg
    simpa only [d61138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1433 (p : Pattern) (guard : d61139 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61138 p = 1 := by simpa only [d61139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1432 p hg
    simpa only [d61139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1434 (p : Pattern) (guard : d61140 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61139 p = 1 := by simpa only [d61140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1433 p hg
    simpa only [d61140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1435 (p : Pattern) (guard : d61141 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61140 p = 1 := by simpa only [d61141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d61141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1436 (p : Pattern) (guard : d61142 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61141 p = 1 := by simpa only [d61142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1435 p hg
    simpa only [d61142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1437 (p : Pattern) (guard : d61143 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61142 p = 1 := by simpa only [d61143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1436 p hg
    simpa only [d61143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1438 (p : Pattern) (guard : d61144 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d61124 p = 1 := by simpa only [d61144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1346 p hg
    simpa only [d61144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61143 p = 1 := by simpa only [d61144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1437 p hg
    simpa only [d61144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1439 (p : Pattern) (guard : d820 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1347 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1440 (p : Pattern) (guard : d821 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1439 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1348 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1441 (p : Pattern) (guard : d822 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1440 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1442 (p : Pattern) (guard : d823 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1441 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1443 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (-1 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1444 (p : Pattern) (guard : d1084 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1443 p hg
    simpa only [d1084, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1213 p hg
    simpa only [d1084, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1445 (p : Pattern) (guard : d1085 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1444 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1446 (p : Pattern) (guard : d1086 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1445 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1447 (p : Pattern) (guard : d1087 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1446 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1448 (p : Pattern) (guard : d1088 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1349 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1447 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1449 (p : Pattern) (guard : d1089 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1448 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1450 (p : Pattern) (guard : d1090 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1442 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1449 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1451 (p : Pattern) (guard : d825 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1452 (p : Pattern) (guard : d826 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1347 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1451 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1453 (p : Pattern) (guard : d827 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1452 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1354 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1454 (p : Pattern) (guard : d828 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1453 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1455 (p : Pattern) (guard : d829 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1454 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1456 (p : Pattern) (guard : d830 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1455 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1357 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1457 (p : Pattern) (guard : d1091 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1450 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1456 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1458 (p : Pattern) (guard : d1092 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1457 p hg
    simpa only [d1092, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d1092, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1459 (p : Pattern) (guard : d1093 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1446 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1142 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1460 (p : Pattern) (guard : d1094 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1280 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1459 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1461 (p : Pattern) (guard : d1095 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1460 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1462 (p : Pattern) (guard : d1096 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1449 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1461 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1463 (p : Pattern) (guard : d1097 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1462 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1358 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1464 (p : Pattern) (guard : d1098 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1463 p hg
    simpa only [d1098, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d1098, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1465 (p : Pattern) (guard : d1099 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1458 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1464 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1466 (p : Pattern) (guard : d1380 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1380, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d1380, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1099 p = 1 := by simpa only [d1380, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1465 p hg
    simpa only [d1380, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1467 (p : Pattern) (guard : d820 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1363 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1468 (p : Pattern) (guard : d821 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1467 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1364 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1469 (p : Pattern) (guard : d822 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1468 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1470 (p : Pattern) (guard : d823 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1469 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1471 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (-1 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1472 (p : Pattern) (guard : d1084 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1471 p hg
    simpa only [d1084, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1227 p hg
    simpa only [d1084, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1473 (p : Pattern) (guard : d1085 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1472 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1474 (p : Pattern) (guard : d1086 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1473 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1475 (p : Pattern) (guard : d1087 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1474 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1476 (p : Pattern) (guard : d1088 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1365 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1475 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1477 (p : Pattern) (guard : d1089 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1476 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1478 (p : Pattern) (guard : d1090 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1470 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1477 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1479 (p : Pattern) (guard : d825 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1291 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1480 (p : Pattern) (guard : d826 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1363 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1479 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1481 (p : Pattern) (guard : d827 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1480 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1370 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1482 (p : Pattern) (guard : d828 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1481 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1483 (p : Pattern) (guard : d829 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1482 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1484 (p : Pattern) (guard : d830 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1483 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1373 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1485 (p : Pattern) (guard : d1091 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1478 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1484 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1486 (p : Pattern) (guard : d1092 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1485 p hg
    simpa only [d1092, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d1092, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1487 (p : Pattern) (guard : d1093 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1474 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1158 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1488 (p : Pattern) (guard : d1094 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1294 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1487 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1489 (p : Pattern) (guard : d1095 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1488 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1490 (p : Pattern) (guard : d1096 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1477 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1489 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1491 (p : Pattern) (guard : d1097 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1490 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1374 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1492 (p : Pattern) (guard : d1098 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1491 p hg
    simpa only [d1098, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d1098, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1493 (p : Pattern) (guard : d1099 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1486 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1492 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1494 (p : Pattern) (guard : d1100 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1493 p hg
    simpa only [d1100, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d1100, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1495 (p : Pattern) (guard : d1381 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1380 p = 1 := by simpa only [d1381, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1466 p hg
    simpa only [d1381, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1100 p = 1 := by simpa only [d1381, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1494 p hg
    simpa only [d1381, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1496 (p : Pattern) (guard : d17953 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1381 p = 1 := by simpa only [d17953, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1495 p hg
    simpa only [d17953, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17953, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d17953, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1497 (p : Pattern) (guard : d17954 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17953 p = 1 := by simpa only [d17954, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1496 p hg
    simpa only [d17954, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17954, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d17954, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1498 (p : Pattern) (guard : d1104 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1217 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1143 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1499 (p : Pattern) (guard : d1105 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
