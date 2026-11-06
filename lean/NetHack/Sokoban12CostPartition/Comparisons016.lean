/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2240 (p : Pattern) (guard : d828 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare2241 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2242 (p : Pattern) (guard : d1017 p = 1) : d109 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d1017, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2240 p hg
    simpa only [d1017, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1017, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2241 p hg
    simpa only [d1017, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2243 (p : Pattern) (guard : d1017 p = 1) : d227 p ≤ (2 : Int) + d13 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d227, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2239 p hg
    simpa only [d227, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d227, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2242 p hg
    simpa only [d227, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2244 (p : Pattern) (guard : d1017 p = 1) : d227 p ≤ (2 : Int) + d227 p := by
  omega
theorem compare2245 (p : Pattern) (guard : d1017 p = 1) : d227 p ≤ (2 : Int) + d1018 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2243 p hg
    simpa only [d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2244 p hg
    simpa only [d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2246 (p : Pattern) (guard : d1017 p = 1) : d55 p ≤ (2 : Int) + d55 p := by
  omega
theorem compare2247 (p : Pattern) (guard : d1017 p = 1) : d229 p ≤ (2 : Int) + d832 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d229, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2239 p hg
    simpa only [d229, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d229, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2246 p hg
    simpa only [d229, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2248 (p : Pattern) (guard : d1017 p = 1) : d65 p ≤ (2 : Int) + d65 p := by
  omega
theorem compare2249 (p : Pattern) (guard : d1017 p = 1) : d230 p ≤ (2 : Int) + d833 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d230, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2242 p hg
    simpa only [d230, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d230, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2248 p hg
    simpa only [d230, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2250 (p : Pattern) (guard : d1017 p = 1) : d231 p ≤ (2 : Int) + d834 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d231, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2247 p hg
    simpa only [d231, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d231, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2249 p hg
    simpa only [d231, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2251 (p : Pattern) (guard : d1017 p = 1) : d231 p ≤ (2 : Int) + d231 p := by
  omega
theorem compare2252 (p : Pattern) (guard : d1017 p = 1) : d231 p ≤ (2 : Int) + d1019 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2250 p hg
    simpa only [d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2251 p hg
    simpa only [d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2253 (p : Pattern) (guard : d1017 p = 1) : d366 p ≤ (2 : Int) + d1020 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d366, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2245 p hg
    simpa only [d366, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d366, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2252 p hg
    simpa only [d366, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2254 (p : Pattern) (guard : d1017 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  omega
theorem compare2255 (p : Pattern) (guard : d1017 p = 1) : d367 p ≤ (2 : Int) + d1021 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d367, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2252 p hg
    simpa only [d367, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d367, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2254 p hg
    simpa only [d367, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2256 (p : Pattern) (guard : d1017 p = 1) : d368 p ≤ (2 : Int) + d1022 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d368, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2253 p hg
    simpa only [d368, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d368, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2255 p hg
    simpa only [d368, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2257 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (2 : Int) + d119 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2258 (p : Pattern) (guard : d1017 p = 1) : d106 p ≤ (2 : Int) + d1023 p := by
  cases selected : p 160 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d1017, d106, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2238 p hg
    simpa only [d1017, d106, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1017, d106, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2257 p hg
    simpa only [d1017, d106, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2259 (p : Pattern) (guard : d1017 p = 1) : d106 p ≤ (2 : Int) + d1024 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2239 p hg
    simpa only [d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2258 p hg
    simpa only [d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2260 (p : Pattern) (guard : d1017 p = 1) : d106 p ≤ (2 : Int) + d1025 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2239 p hg
    simpa only [d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2259 p hg
    simpa only [d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2261 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (2 : Int) + d502 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2262 (p : Pattern) (guard : d1017 p = 1) : d109 p ≤ (2 : Int) + d1026 p := by
  cases selected : p 160 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d1017, d109, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2240 p hg
    simpa only [d1017, d109, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1017, d109, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2261 p hg
    simpa only [d1017, d109, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2263 (p : Pattern) (guard : d1017 p = 1) : d109 p ≤ (2 : Int) + d1027 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2242 p hg
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2262 p hg
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2264 (p : Pattern) (guard : d1017 p = 1) : d109 p ≤ (2 : Int) + d1028 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2242 p hg
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2263 p hg
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2265 (p : Pattern) (guard : d1017 p = 1) : d227 p ≤ (2 : Int) + d1029 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d227, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2260 p hg
    simpa only [d227, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d227, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2264 p hg
    simpa only [d227, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2266 (p : Pattern) (guard : d1017 p = 1) : d369 p ≤ (2 : Int) + d1030 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d369, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2265 p hg
    simpa only [d369, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d369, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2254 p hg
    simpa only [d369, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2267 (p : Pattern) (guard : d1017 p = 1) : d229 p ≤ (2 : Int) + d1031 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d229, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2258 p hg
    simpa only [d229, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d229, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2246 p hg
    simpa only [d229, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2268 (p : Pattern) (guard : d1017 p = 1) : d230 p ≤ (2 : Int) + d1032 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d230, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2262 p hg
    simpa only [d230, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d230, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2248 p hg
    simpa only [d230, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2269 (p : Pattern) (guard : d1017 p = 1) : d231 p ≤ (2 : Int) + d1033 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d231, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2267 p hg
    simpa only [d231, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d231, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2268 p hg
    simpa only [d231, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2270 (p : Pattern) (guard : d1017 p = 1) : d370 p ≤ (2 : Int) + d1034 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d370, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2269 p hg
    simpa only [d370, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d370, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2254 p hg
    simpa only [d370, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2271 (p : Pattern) (guard : d1017 p = 1) : d371 p ≤ (2 : Int) + d1035 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d371, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2266 p hg
    simpa only [d371, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d371, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2270 p hg
    simpa only [d371, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2272 (p : Pattern) (guard : d1017 p = 1) : d229 p ≤ (2 : Int) + d1036 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d229, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2259 p hg
    simpa only [d229, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d229, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2246 p hg
    simpa only [d229, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2273 (p : Pattern) (guard : d1017 p = 1) : d230 p ≤ (2 : Int) + d1037 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d230, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2263 p hg
    simpa only [d230, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d230, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2248 p hg
    simpa only [d230, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2274 (p : Pattern) (guard : d1017 p = 1) : d231 p ≤ (2 : Int) + d1038 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d231, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2272 p hg
    simpa only [d231, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d231, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2273 p hg
    simpa only [d231, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2275 (p : Pattern) (guard : d1017 p = 1) : d370 p ≤ (2 : Int) + d1039 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d370, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2274 p hg
    simpa only [d370, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d370, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2254 p hg
    simpa only [d370, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2276 (p : Pattern) (guard : d1017 p = 1) : d372 p ≤ (2 : Int) + d1040 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d372, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2275 p hg
    simpa only [d372, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d372, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2254 p hg
    simpa only [d372, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2277 (p : Pattern) (guard : d1017 p = 1) : d373 p ≤ (2 : Int) + d1041 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d373, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2271 p hg
    simpa only [d373, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d373, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2276 p hg
    simpa only [d373, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2278 (p : Pattern) (guard : d1017 p = 1) : d374 p ≤ (2 : Int) + d1042 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d374, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2256 p hg
    simpa only [d374, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d374, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2277 p hg
    simpa only [d374, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2279 (p : Pattern) (guard : d758 p = 1) : d227 p ≤ (0 : Int) + d228 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2171 p hg
    simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare883 p hg
    simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2280 (p : Pattern) (guard : d758 p = 1) : d231 p ≤ (0 : Int) + d232 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2175 p hg
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare885 p hg
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2281 (p : Pattern) (guard : d758 p = 1) : d366 p ≤ (0 : Int) + d233 p := by
  cases selected : p 133 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d366, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2279 p hg
    simpa only [d366, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d366, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2280 p hg
    simpa only [d366, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2282 (p : Pattern) (guard : d758 p = 1) : d367 p ≤ (0 : Int) + d234 p := by
  cases selected : p 133 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d367, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2280 p hg
    simpa only [d367, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d367, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare888 p hg
    simpa only [d367, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2283 (p : Pattern) (guard : d758 p = 1) : d368 p ≤ (0 : Int) + d235 p := by
  cases selected : p 132 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d368, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2281 p hg
    simpa only [d368, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d368, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2282 p hg
    simpa only [d368, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2284 (p : Pattern) (guard : d758 p = 1) : d369 p ≤ (0 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2171 p hg
    simpa only [d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare888 p hg
    simpa only [d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2285 (p : Pattern) (guard : d758 p = 1) : d370 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d370, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2175 p hg
    simpa only [d370, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d370, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare888 p hg
    simpa only [d370, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2286 (p : Pattern) (guard : d758 p = 1) : d371 p ≤ (0 : Int) + d72 p := by
  cases selected : p 133 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d371, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2284 p hg
    simpa only [d371, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d371, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2285 p hg
    simpa only [d371, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2287 (p : Pattern) (guard : d758 p = 1) : d372 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d372, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2285 p hg
    simpa only [d372, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d372, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare888 p hg
    simpa only [d372, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2288 (p : Pattern) (guard : d758 p = 1) : d373 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d373, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2286 p hg
    simpa only [d373, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d373, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2287 p hg
    simpa only [d373, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2289 (p : Pattern) (guard : d758 p = 1) : d374 p ≤ (0 : Int) + d236 p := by
  cases selected : p 108 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d374, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2283 p hg
    simpa only [d374, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d374, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2288 p hg
    simpa only [d374, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2290 (p : Pattern) (guard : d818 p = 1) : d106 p ≤ (0 : Int) + d114 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2169 p hg
    simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare476 p hg
    simpa only [d818, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2291 (p : Pattern) (guard : d818 p = 1) : d109 p ≤ (0 : Int) + d116 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2170 p hg
    simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare480 p hg
    simpa only [d818, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2292 (p : Pattern) (guard : d818 p = 1) : d227 p ≤ (0 : Int) + d335 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d227, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2290 p hg
    simpa only [d227, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d227, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2291 p hg
    simpa only [d227, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2293 (p : Pattern) (guard : d818 p = 1) : d106 p ≤ (0 : Int) + d107 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare690 p hg
    simpa only [d818, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare476 p hg
    simpa only [d818, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2294 (p : Pattern) (guard : d818 p = 1) : d109 p ≤ (0 : Int) + d110 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare695 p hg
    simpa only [d818, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare480 p hg
    simpa only [d818, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2295 (p : Pattern) (guard : d818 p = 1) : d227 p ≤ (0 : Int) + d336 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d227, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2293 p hg
    simpa only [d227, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d227, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2294 p hg
    simpa only [d227, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2296 (p : Pattern) (guard : d818 p = 1) : d227 p ≤ (0 : Int) + d337 p := by
  cases selected : p 134 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2292 p hg
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2295 p hg
    simpa only [d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2297 (p : Pattern) (guard : d818 p = 1) : d229 p ≤ (0 : Int) + d338 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d229, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2290 p hg
    simpa only [d229, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d229, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare707 p hg
    simpa only [d229, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2298 (p : Pattern) (guard : d818 p = 1) : d230 p ≤ (0 : Int) + d339 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d230, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2291 p hg
    simpa only [d230, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d230, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d230, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2299 (p : Pattern) (guard : d818 p = 1) : d231 p ≤ (0 : Int) + d340 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d231, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2297 p hg
    simpa only [d231, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d231, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2298 p hg
    simpa only [d231, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2300 (p : Pattern) (guard : d818 p = 1) : d229 p ≤ (0 : Int) + d211 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d229, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2293 p hg
    simpa only [d229, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d229, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare707 p hg
    simpa only [d229, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2301 (p : Pattern) (guard : d818 p = 1) : d230 p ≤ (0 : Int) + d212 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d230, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2294 p hg
    simpa only [d230, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d230, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d230, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2302 (p : Pattern) (guard : d818 p = 1) : d231 p ≤ (0 : Int) + d213 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d231, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2300 p hg
    simpa only [d231, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d231, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2301 p hg
    simpa only [d231, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2303 (p : Pattern) (guard : d818 p = 1) : d231 p ≤ (0 : Int) + d341 p := by
  cases selected : p 134 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2299 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2302 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2304 (p : Pattern) (guard : d818 p = 1) : d366 p ≤ (0 : Int) + d342 p := by
  cases selected : p 133 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d366, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2296 p hg
    simpa only [d366, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d366, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2303 p hg
    simpa only [d366, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2305 (p : Pattern) (guard : d818 p = 1) : d367 p ≤ (0 : Int) + d343 p := by
  cases selected : p 133 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d367, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2303 p hg
    simpa only [d367, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d367, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d367, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2306 (p : Pattern) (guard : d818 p = 1) : d368 p ≤ (0 : Int) + d344 p := by
  cases selected : p 132 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d368, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2304 p hg
    simpa only [d368, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d368, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2305 p hg
    simpa only [d368, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2307 (p : Pattern) (guard : d818 p = 1) : d369 p ≤ (0 : Int) + d345 p := by
  cases selected : p 134 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d369, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2292 p hg
    simpa only [d369, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d369, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d369, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2308 (p : Pattern) (guard : d758 p = 1) : d106 p ≤ (0 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d106, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d758, d106, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d106, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2216 p hg
    simpa only [d758, d106, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2309 (p : Pattern) (guard : d818 p = 1) : d106 p ≤ (0 : Int) + d346 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2308 p hg
    simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare476 p hg
    simpa only [d818, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2310 (p : Pattern) (guard : d818 p = 1) : d229 p ≤ (0 : Int) + d347 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d229, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2309 p hg
    simpa only [d229, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d229, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare707 p hg
    simpa only [d229, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2311 (p : Pattern) (guard : d758 p = 1) : d109 p ≤ (0 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d109, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare294 p hg
    simpa only [d758, d109, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d109, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2220 p hg
    simpa only [d758, d109, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2312 (p : Pattern) (guard : d818 p = 1) : d109 p ≤ (0 : Int) + d348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2311 p hg
    simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare480 p hg
    simpa only [d818, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2313 (p : Pattern) (guard : d818 p = 1) : d230 p ≤ (0 : Int) + d349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d230, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2312 p hg
    simpa only [d230, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d230, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d230, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2314 (p : Pattern) (guard : d818 p = 1) : d231 p ≤ (0 : Int) + d350 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d231, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2310 p hg
    simpa only [d231, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d231, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2313 p hg
    simpa only [d231, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2315 (p : Pattern) (guard : d818 p = 1) : d370 p ≤ (0 : Int) + d351 p := by
  cases selected : p 134 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d370, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2314 p hg
    simpa only [d370, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d370, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d370, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2316 (p : Pattern) (guard : d818 p = 1) : d371 p ≤ (0 : Int) + d352 p := by
  cases selected : p 133 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d371, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2307 p hg
    simpa only [d371, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d371, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2315 p hg
    simpa only [d371, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2317 (p : Pattern) (guard : d818 p = 1) : d370 p ≤ (0 : Int) + d353 p := by
  cases selected : p 134 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d370, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2299 p hg
    simpa only [d370, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d370, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d370, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2318 (p : Pattern) (guard : d818 p = 1) : d372 p ≤ (0 : Int) + d354 p := by
  cases selected : p 133 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d372, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d372, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d372, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d372, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2319 (p : Pattern) (guard : d818 p = 1) : d373 p ≤ (0 : Int) + d355 p := by
  cases selected : p 132 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d373, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2316 p hg
    simpa only [d373, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d373, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d373, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2320 (p : Pattern) (guard : d818 p = 1) : d374 p ≤ (0 : Int) + d356 p := by
  cases selected : p 108 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d374, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2306 p hg
    simpa only [d374, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d374, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2319 p hg
    simpa only [d374, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2321 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (2 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2322 (p : Pattern) (guard : d758 p = 1) : d106 p ≤ (2 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare115 p hg
    simpa only [d758, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare167 p hg
    simpa only [d758, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2323 (p : Pattern) (guard : d1000 p = 1) : d106 p ≤ (2 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2321 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2322 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2324 (p : Pattern) (guard : d1001 p = 1) : d106 p ≤ (2 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2323 p hg
    simpa only [d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2321 p hg
    simpa only [d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2325 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (2 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2326 (p : Pattern) (guard : d758 p = 1) : d109 p ≤ (2 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare857 p hg
    simpa only [d758, d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare169 p hg
    simpa only [d758, d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2327 (p : Pattern) (guard : d1000 p = 1) : d109 p ≤ (2 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2325 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2326 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2328 (p : Pattern) (guard : d1001 p = 1) : d109 p ≤ (2 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2327 p hg
    simpa only [d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2325 p hg
    simpa only [d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2329 (p : Pattern) (guard : d1001 p = 1) : d227 p ≤ (2 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d227, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2324 p hg
    simpa only [d227, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d227, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2328 p hg
    simpa only [d227, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2330 (p : Pattern) (guard : d1001 p = 1) : d227 p ≤ (2 : Int) + d227 p := by
  omega
theorem compare2331 (p : Pattern) (guard : d1001 p = 1) : d227 p ≤ (2 : Int) + d228 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2329 p hg
    simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2330 p hg
    simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2332 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (2 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2333 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (2 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2334 (p : Pattern) (guard : d758 p = 1) : d106 p ≤ (2 : Int) + d55 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8 p hg
    simpa only [d758, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2333 p hg
    simpa only [d758, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2335 (p : Pattern) (guard : d1000 p = 1) : d106 p ≤ (2 : Int) + d55 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2332 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2334 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2336 (p : Pattern) (guard : d1001 p = 1) : d229 p ≤ (2 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2335 p hg
    simpa only [d1001, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2333 p hg
    simpa only [d1001, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2337 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (2 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2338 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (2 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2339 (p : Pattern) (guard : d758 p = 1) : d109 p ≤ (2 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18 p hg
    simpa only [d758, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2338 p hg
    simpa only [d758, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2340 (p : Pattern) (guard : d1000 p = 1) : d109 p ≤ (2 : Int) + d65 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2337 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2339 p hg
    simpa only [d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2341 (p : Pattern) (guard : d1001 p = 1) : d230 p ≤ (2 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1000 p = 1 := by simpa only [d1001, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2340 p hg
    simpa only [d1001, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1001, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2338 p hg
    simpa only [d1001, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2342 (p : Pattern) (guard : d1001 p = 1) : d231 p ≤ (2 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d231, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2336 p hg
    simpa only [d231, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d231, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2341 p hg
    simpa only [d231, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2343 (p : Pattern) (guard : d1001 p = 1) : d366 p ≤ (2 : Int) + d1043 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d366, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2331 p hg
    simpa only [d366, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d366, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2342 p hg
    simpa only [d366, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2344 (p : Pattern) (guard : d1001 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  omega
theorem compare2345 (p : Pattern) (guard : d1001 p = 1) : d367 p ≤ (2 : Int) + d66 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2342 p hg
    simpa only [d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2344 p hg
    simpa only [d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2346 (p : Pattern) (guard : d1001 p = 1) : d368 p ≤ (2 : Int) + d1044 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d368, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2343 p hg
    simpa only [d368, d1044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d368, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2345 p hg
    simpa only [d368, d1044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2347 (p : Pattern) (guard : d1001 p = 1) : d369 p ≤ (2 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2329 p hg
    simpa only [d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2344 p hg
    simpa only [d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2348 (p : Pattern) (guard : d1001 p = 1) : d370 p ≤ (2 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2342 p hg
    simpa only [d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2344 p hg
    simpa only [d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2349 (p : Pattern) (guard : d1001 p = 1) : d371 p ≤ (2 : Int) + d217 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d371, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2347 p hg
    simpa only [d371, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d371, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d371, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2350 (p : Pattern) (guard : d1001 p = 1) : d372 p ≤ (2 : Int) + d66 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2344 p hg
    simpa only [d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2351 (p : Pattern) (guard : d1001 p = 1) : d373 p ≤ (2 : Int) + d1045 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d373, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2349 p hg
    simpa only [d373, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d373, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2350 p hg
    simpa only [d373, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2352 (p : Pattern) (guard : d1001 p = 1) : d374 p ≤ (2 : Int) + d1046 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1001 p = 1 := by simpa only [d374, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2346 p hg
    simpa only [d374, d1046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1001 p = 1 := by simpa only [d374, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2351 p hg
    simpa only [d374, d1046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2353 (p : Pattern) (guard : d818 p = 1) : d106 p ≤ (0 : Int) + d108 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare689 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2293 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2354 (p : Pattern) (guard : d818 p = 1) : d109 p ≤ (0 : Int) + d111 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare694 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2294 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2355 (p : Pattern) (guard : d818 p = 1) : d227 p ≤ (0 : Int) + d112 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d227, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2353 p hg
    simpa only [d227, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d227, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2354 p hg
    simpa only [d227, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2356 (p : Pattern) (guard : d819 p = 1) : d227 p ≤ (0 : Int) + d113 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d819, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2171 p hg
    simpa only [d819, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d819, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2355 p hg
    simpa only [d819, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2357 (p : Pattern) (guard : d820 p = 1) : d366 p ≤ (0 : Int) + d210 p := by
  cases selected : p 133 with
  | false =>
    have hg : d819 p = 1 := by simpa only [d820, d366, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2356 p hg
    simpa only [d820, d366, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d820, d366, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare847 p hg
    simpa only [d820, d366, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2358 (p : Pattern) (guard : d819 p = 1) : d231 p ≤ (0 : Int) + d214 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d819, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2175 p hg
    simpa only [d819, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d819, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2302 p hg
    simpa only [d819, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2359 (p : Pattern) (guard : d820 p = 1) : d367 p ≤ (0 : Int) + d215 p := by
  cases selected : p 133 with
  | false =>
    have hg : d819 p = 1 := by simpa only [d820, d367, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2358 p hg
    simpa only [d820, d367, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d820, d367, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d820, d367, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2360 (p : Pattern) (guard : d820 p = 1) : d368 p ≤ (0 : Int) + d216 p := by
  cases selected : p 132 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d368, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2357 p hg
    simpa only [d368, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d368, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2359 p hg
    simpa only [d368, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2361 (p : Pattern) (guard : d819 p = 1) : d369 p ≤ (0 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d819, d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2171 p hg
    simpa only [d819, d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d819, d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d819, d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2362 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2363 (p : Pattern) (guard : d820 p = 1) : d371 p ≤ (0 : Int) + d217 p := by
  cases selected : p 133 with
  | false =>
    have hg : d819 p = 1 := by simpa only [d820, d371, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2361 p hg
    simpa only [d820, d371, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d820, d371, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2362 p hg
    simpa only [d820, d371, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2364 (p : Pattern) (guard : d819 p = 1) : d370 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d819, d370, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2175 p hg
    simpa only [d819, d370, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d819, d370, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d819, d370, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2365 (p : Pattern) (guard : d820 p = 1) : d372 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d819 p = 1 := by simpa only [d820, d372, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2364 p hg
    simpa only [d820, d372, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d820, d372, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d820, d372, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2366 (p : Pattern) (guard : d820 p = 1) : d373 p ≤ (0 : Int) + d218 p := by
  cases selected : p 132 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d373, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2363 p hg
    simpa only [d373, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d373, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2365 p hg
    simpa only [d373, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2367 (p : Pattern) (guard : d820 p = 1) : d374 p ≤ (0 : Int) + d219 p := by
  cases selected : p 108 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d374, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2360 p hg
    simpa only [d374, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d374, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2366 p hg
    simpa only [d374, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2368 (p : Pattern) (guard : d851 p = 1) : d7 p ≤ (0 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2108 p hg
    simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2369 (p : Pattern) (guard : d1047 p = 1) : d106 p ≤ (0 : Int) + d501 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1047, d106, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d1047, d106, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1047, d106, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2216 p hg
    simpa only [d1047, d106, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2370 (p : Pattern) (guard : d851 p = 1) : d11 p ≤ (0 : Int) + d125 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2113 p hg
    simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2371 (p : Pattern) (guard : d851 p = 1) : d12 p ≤ (0 : Int) + d502 p := by
  cases selected : p 168 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d12, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d12, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d12, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2370 p hg
    simpa only [d12, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2372 (p : Pattern) (guard : d1047 p = 1) : d109 p ≤ (0 : Int) + d503 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1047, d109, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d1047, d109, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1047, d109, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2220 p hg
    simpa only [d1047, d109, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2373 (p : Pattern) (guard : d1047 p = 1) : d227 p ≤ (0 : Int) + d504 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d227, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2369 p hg
    simpa only [d227, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d227, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2372 p hg
    simpa only [d227, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2374 (p : Pattern) (guard : d1047 p = 1) : d106 p ≤ (0 : Int) + d505 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1047, d106, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d1047, d106, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1047, d106, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1047, d106, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2375 (p : Pattern) (guard : d1047 p = 1) : d109 p ≤ (0 : Int) + d506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1047, d109, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d1047, d109, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1047, d109, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d1047, d109, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2376 (p : Pattern) (guard : d1047 p = 1) : d227 p ≤ (0 : Int) + d507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d227, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2374 p hg
    simpa only [d227, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d227, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2375 p hg
    simpa only [d227, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2377 (p : Pattern) (guard : d1047 p = 1) : d227 p ≤ (0 : Int) + d508 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2373 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2376 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2378 (p : Pattern) (guard : d1047 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare2379 (p : Pattern) (guard : d1047 p = 1) : d229 p ≤ (0 : Int) + d509 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d229, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2369 p hg
    simpa only [d229, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d229, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2378 p hg
    simpa only [d229, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
