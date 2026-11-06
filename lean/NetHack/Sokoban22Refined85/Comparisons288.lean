/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons287
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare40320 (p : Pattern) (guard : d8107 p = 1) : d2220 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2220, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40319 p hg
    simpa only [d8107, d2220, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2220, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40184 p hg
    simpa only [d8107, d2220, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40321 (p : Pattern) (guard : d8108 p = 1) : d2221 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2221, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40318 p hg
    simpa only [d8108, d2221, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2221, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40320 p hg
    simpa only [d8108, d2221, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40322 (p : Pattern) (guard : d8114 p = 1) : d2227 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2227, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40321 p hg
    simpa only [d8114, d2227, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2227, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40190 p hg
    simpa only [d8114, d2227, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40323 (p : Pattern) (guard : d8115 p = 1) : d2303 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2303, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40315 p hg
    simpa only [d8115, d2303, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2303, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40322 p hg
    simpa only [d8115, d2303, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40324 (p : Pattern) (guard : d8085 p = 1) : d330 p ≤ (0 : Int) + d330 p := by
  omega
theorem compare40325 (p : Pattern) (guard : d8086 p = 1) : d2189 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2189, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34333 p hg
    simpa only [d8086, d2189, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2189, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40324 p hg
    simpa only [d8086, d2189, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40326 (p : Pattern) (guard : d8091 p = 1) : d2190 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2190, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40325 p hg
    simpa only [d8091, d2190, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2190, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40208 p hg
    simpa only [d8091, d2190, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40327 (p : Pattern) (guard : d8095 p = 1) : d2187 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2187, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40253 p hg
    simpa only [d8095, d2187, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2187, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2187, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40328 (p : Pattern) (guard : d8096 p = 1) : d2191 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2191, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40326 p hg
    simpa only [d8096, d2191, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2191, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40327 p hg
    simpa only [d8096, d2191, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40329 (p : Pattern) (guard : d8090 p = 1) : d2209 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2209, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34785 p hg
    simpa only [d8090, d2209, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2209, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2209, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40330 (p : Pattern) (guard : d8095 p = 1) : d2209 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40329 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40052 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40331 (p : Pattern) (guard : d8101 p = 1) : d2232 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2232, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40330 p hg
    simpa only [d8101, d2232, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2232, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40106 p hg
    simpa only [d8101, d2232, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40332 (p : Pattern) (guard : d8102 p = 1) : d2304 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2304, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40328 p hg
    simpa only [d8102, d2304, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2304, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40331 p hg
    simpa only [d8102, d2304, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40333 (p : Pattern) (guard : d8090 p = 1) : d2196 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2196, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34790 p hg
    simpa only [d8090, d2196, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2196, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2196, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40334 (p : Pattern) (guard : d8095 p = 1) : d2196 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40333 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39999 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40335 (p : Pattern) (guard : d8101 p = 1) : d2198 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2198, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40334 p hg
    simpa only [d8101, d2198, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2198, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40077 p hg
    simpa only [d8101, d2198, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40336 (p : Pattern) (guard : d8094 p = 1) : d2203 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2203, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34795 p hg
    simpa only [d8094, d2203, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2203, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2203, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40337 (p : Pattern) (guard : d8100 p = 1) : d2203 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40336 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40056 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40338 (p : Pattern) (guard : d8106 p = 1) : d2205 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2205, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40337 p hg
    simpa only [d8106, d2205, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2205, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40112 p hg
    simpa only [d8106, d2205, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40339 (p : Pattern) (guard : d8107 p = 1) : d2234 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2234, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40335 p hg
    simpa only [d8107, d2234, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2234, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40338 p hg
    simpa only [d8107, d2234, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40340 (p : Pattern) (guard : d8108 p = 1) : d2305 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2305, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40332 p hg
    simpa only [d8108, d2305, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2305, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40339 p hg
    simpa only [d8108, d2305, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40341 (p : Pattern) (guard : d8094 p = 1) : d2236 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2236, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34803 p hg
    simpa only [d8094, d2236, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2236, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2236, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40342 (p : Pattern) (guard : d8100 p = 1) : d2236 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40341 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40061 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40343 (p : Pattern) (guard : d8106 p = 1) : d2238 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2238, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40342 p hg
    simpa only [d8106, d2238, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2238, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40116 p hg
    simpa only [d8106, d2238, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40344 (p : Pattern) (guard : d8107 p = 1) : d2239 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2239, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40306 p hg
    simpa only [d8107, d2239, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2239, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40343 p hg
    simpa only [d8107, d2239, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40345 (p : Pattern) (guard : d8113 p = 1) : d2242 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2242, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40344 p hg
    simpa only [d8113, d2242, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2242, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40121 p hg
    simpa only [d8113, d2242, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40346 (p : Pattern) (guard : d8114 p = 1) : d2306 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2306, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40340 p hg
    simpa only [d8114, d2306, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2306, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40345 p hg
    simpa only [d8114, d2306, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40347 (p : Pattern) (guard : d8101 p = 1) : d2214 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2214, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40283 p hg
    simpa only [d8101, d2214, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2214, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40092 p hg
    simpa only [d8101, d2214, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40348 (p : Pattern) (guard : d8107 p = 1) : d2245 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2245, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40347 p hg
    simpa only [d8107, d2245, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2245, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40213 p hg
    simpa only [d8107, d2245, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40349 (p : Pattern) (guard : d8113 p = 1) : d2247 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2247, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40348 p hg
    simpa only [d8113, d2247, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2247, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40218 p hg
    simpa only [d8113, d2247, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40350 (p : Pattern) (guard : d8119 p = 1) : d2253 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2253, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40349 p hg
    simpa only [d8119, d2253, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2253, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40228 p hg
    simpa only [d8119, d2253, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40351 (p : Pattern) (guard : d8120 p = 1) : d2307 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2307, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40346 p hg
    simpa only [d8120, d2307, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2307, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40350 p hg
    simpa only [d8120, d2307, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40352 (p : Pattern) (guard : d8121 p = 1) : d2308 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d2308, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40323 p hg
    simpa only [d8121, d2308, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d2308, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40351 p hg
    simpa only [d8121, d2308, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40353 (p : Pattern) (guard : d8102 p = 1) : d2201 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40144 p hg
    simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40284 p hg
    simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40354 (p : Pattern) (guard : d8107 p = 1) : d2202 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2202, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40255 p hg
    simpa only [d8107, d2202, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2202, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40237 p hg
    simpa only [d8107, d2202, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40355 (p : Pattern) (guard : d8108 p = 1) : d2256 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2256, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40353 p hg
    simpa only [d8108, d2256, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2256, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40354 p hg
    simpa only [d8108, d2256, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40356 (p : Pattern) (guard : d8113 p = 1) : d2207 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2207, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40278 p hg
    simpa only [d8113, d2207, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2207, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40240 p hg
    simpa only [d8113, d2207, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40357 (p : Pattern) (guard : d8114 p = 1) : d2257 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2257, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40355 p hg
    simpa only [d8114, d2257, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2257, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40356 p hg
    simpa only [d8114, d2257, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40358 (p : Pattern) (guard : d8120 p = 1) : d2262 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2262, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40357 p hg
    simpa only [d8120, d2262, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2262, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40251 p hg
    simpa only [d8120, d2262, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40359 (p : Pattern) (guard : d8090 p = 1) : d2185 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34827 p hg
    simpa only [d8090, d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40360 (p : Pattern) (guard : d8095 p = 1) : d2185 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40359 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40177 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40361 (p : Pattern) (guard : d8101 p = 1) : d2201 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2201, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40360 p hg
    simpa only [d8101, d2201, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2201, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40232 p hg
    simpa only [d8101, d2201, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40362 (p : Pattern) (guard : d8094 p = 1) : d2209 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34832 p hg
    simpa only [d8094, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40363 (p : Pattern) (guard : d8100 p = 1) : d2209 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40362 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40211 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40364 (p : Pattern) (guard : d8106 p = 1) : d2232 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40363 p hg
    simpa only [d8106, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40256 p hg
    simpa only [d8106, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40365 (p : Pattern) (guard : d8107 p = 1) : d2263 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2263, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40361 p hg
    simpa only [d8107, d2263, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2263, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40364 p hg
    simpa only [d8107, d2263, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40366 (p : Pattern) (guard : d8113 p = 1) : d2264 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2264, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40365 p hg
    simpa only [d8113, d2264, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2264, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40261 p hg
    simpa only [d8113, d2264, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40367 (p : Pattern) (guard : d8119 p = 1) : d2265 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2265, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40366 p hg
    simpa only [d8119, d2265, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2265, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40269 p hg
    simpa only [d8119, d2265, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40368 (p : Pattern) (guard : d8125 p = 1) : d2269 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2269, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40367 p hg
    simpa only [d8125, d2269, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2269, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40273 p hg
    simpa only [d8125, d2269, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40369 (p : Pattern) (guard : d8126 p = 1) : d2270 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2270, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40358 p hg
    simpa only [d8126, d2270, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2270, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40368 p hg
    simpa only [d8126, d2270, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40370 (p : Pattern) (guard : d8127 p = 1) : d2309 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d2309, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40352 p hg
    simpa only [d8127, d2309, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d2309, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40369 p hg
    simpa only [d8127, d2309, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40371 (p : Pattern) (guard : d8102 p = 1) : d2201 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40195 p hg
    simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40361 p hg
    simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40372 (p : Pattern) (guard : d8107 p = 1) : d2202 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2202, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40284 p hg
    simpa only [d8107, d2202, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2202, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40237 p hg
    simpa only [d8107, d2202, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40373 (p : Pattern) (guard : d8108 p = 1) : d2256 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2256, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40371 p hg
    simpa only [d8108, d2256, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2256, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40372 p hg
    simpa only [d8108, d2256, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40374 (p : Pattern) (guard : d8113 p = 1) : d2207 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2207, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40354 p hg
    simpa only [d8113, d2207, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2207, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40240 p hg
    simpa only [d8113, d2207, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40375 (p : Pattern) (guard : d8114 p = 1) : d2257 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2257, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40373 p hg
    simpa only [d8114, d2257, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2257, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40374 p hg
    simpa only [d8114, d2257, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40376 (p : Pattern) (guard : d8101 p = 1) : d2232 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40053 p hg
    simpa only [d8101, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40106 p hg
    simpa only [d8101, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40377 (p : Pattern) (guard : d8107 p = 1) : d2259 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2259, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40376 p hg
    simpa only [d8107, d2259, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2259, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40248 p hg
    simpa only [d8107, d2259, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40378 (p : Pattern) (guard : d8113 p = 1) : d2260 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2260, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40377 p hg
    simpa only [d8113, d2260, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2260, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40121 p hg
    simpa only [d8113, d2260, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40379 (p : Pattern) (guard : d8119 p = 1) : d2261 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2261, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40378 p hg
    simpa only [d8119, d2261, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2261, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2261, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40380 (p : Pattern) (guard : d8120 p = 1) : d2262 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2262, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40375 p hg
    simpa only [d8120, d2262, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2262, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40379 p hg
    simpa only [d8120, d2262, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40381 (p : Pattern) (guard : d8090 p = 1) : d2185 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34844 p hg
    simpa only [d8090, d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40382 (p : Pattern) (guard : d8095 p = 1) : d2185 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40381 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40177 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40383 (p : Pattern) (guard : d8101 p = 1) : d2201 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2201, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40382 p hg
    simpa only [d8101, d2201, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2201, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40232 p hg
    simpa only [d8101, d2201, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40384 (p : Pattern) (guard : d8094 p = 1) : d2209 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35016 p hg
    simpa only [d8094, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40385 (p : Pattern) (guard : d8100 p = 1) : d2209 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40384 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40211 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40386 (p : Pattern) (guard : d8106 p = 1) : d2232 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40385 p hg
    simpa only [d8106, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40256 p hg
    simpa only [d8106, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40387 (p : Pattern) (guard : d8107 p = 1) : d2263 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2263, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40383 p hg
    simpa only [d8107, d2263, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2263, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40386 p hg
    simpa only [d8107, d2263, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40388 (p : Pattern) (guard : d8094 p = 1) : d2196 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2196, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34850 p hg
    simpa only [d8094, d2196, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2196, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2196, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40389 (p : Pattern) (guard : d8100 p = 1) : d2196 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40388 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40182 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40390 (p : Pattern) (guard : d8106 p = 1) : d2198 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2198, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40389 p hg
    simpa only [d8106, d2198, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2198, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40236 p hg
    simpa only [d8106, d2198, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40391 (p : Pattern) (guard : d8112 p = 1) : d2234 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2234, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40390 p hg
    simpa only [d8112, d2234, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2234, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40260 p hg
    simpa only [d8112, d2234, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40392 (p : Pattern) (guard : d8113 p = 1) : d2264 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2264, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40387 p hg
    simpa only [d8113, d2264, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2264, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40391 p hg
    simpa only [d8113, d2264, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40393 (p : Pattern) (guard : d8119 p = 1) : d2265 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2265, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40392 p hg
    simpa only [d8119, d2265, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2265, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40269 p hg
    simpa only [d8119, d2265, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40394 (p : Pattern) (guard : d8125 p = 1) : d2269 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2269, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40393 p hg
    simpa only [d8125, d2269, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2269, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40273 p hg
    simpa only [d8125, d2269, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40395 (p : Pattern) (guard : d8126 p = 1) : d2270 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2270, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40380 p hg
    simpa only [d8126, d2270, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2270, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40394 p hg
    simpa only [d8126, d2270, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40396 (p : Pattern) (guard : d8107 p = 1) : d2277 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2277, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40312 p hg
    simpa only [d8107, d2277, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2277, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40120 p hg
    simpa only [d8107, d2277, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40397 (p : Pattern) (guard : d8113 p = 1) : d2278 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2278, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40396 p hg
    simpa only [d8113, d2278, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2278, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40121 p hg
    simpa only [d8113, d2278, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40398 (p : Pattern) (guard : d8118 p = 1) : d2279 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40121 p hg
    simpa only [d8118, d2279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40399 (p : Pattern) (guard : d8119 p = 1) : d2280 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2280, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40397 p hg
    simpa only [d8119, d2280, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2280, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40398 p hg
    simpa only [d8119, d2280, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40400 (p : Pattern) (guard : d8124 p = 1) : d2281 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40398 p hg
    simpa only [d8124, d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40401 (p : Pattern) (guard : d8125 p = 1) : d2282 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2282, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40399 p hg
    simpa only [d8125, d2282, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2282, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40400 p hg
    simpa only [d8125, d2282, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40402 (p : Pattern) (guard : d8130 p = 1) : d2283 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40400 p hg
    simpa only [d8130, d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40403 (p : Pattern) (guard : d8131 p = 1) : d2284 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2284, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40401 p hg
    simpa only [d8131, d2284, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2284, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40402 p hg
    simpa only [d8131, d2284, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40404 (p : Pattern) (guard : d8132 p = 1) : d2310 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2310, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40395 p hg
    simpa only [d8132, d2310, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2310, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40403 p hg
    simpa only [d8132, d2310, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40405 (p : Pattern) (guard : d8133 p = 1) : d2311 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d2311, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40370 p hg
    simpa only [d8133, d2311, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d2311, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40404 p hg
    simpa only [d8133, d2311, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40406 (p : Pattern) (guard : d8102 p = 1) : d2272 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2272, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40302 p hg
    simpa only [d8102, d2272, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2272, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40383 p hg
    simpa only [d8102, d2272, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40407 (p : Pattern) (guard : d8107 p = 1) : d2202 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2202, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40361 p hg
    simpa only [d8107, d2202, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2202, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40390 p hg
    simpa only [d8107, d2202, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40408 (p : Pattern) (guard : d8108 p = 1) : d2273 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2273, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40406 p hg
    simpa only [d8108, d2273, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2273, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40407 p hg
    simpa only [d8108, d2273, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40409 (p : Pattern) (guard : d8113 p = 1) : d2207 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2207, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40372 p hg
    simpa only [d8113, d2207, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2207, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40240 p hg
    simpa only [d8113, d2207, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40410 (p : Pattern) (guard : d8114 p = 1) : d2274 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2274, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40408 p hg
    simpa only [d8114, d2274, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2274, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40409 p hg
    simpa only [d8114, d2274, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40411 (p : Pattern) (guard : d8101 p = 1) : d2211 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2211, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40254 p hg
    simpa only [d8101, d2211, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2211, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40106 p hg
    simpa only [d8101, d2211, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40412 (p : Pattern) (guard : d8099 p = 1) : d2185 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34636 p hg
    simpa only [d8099, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40413 (p : Pattern) (guard : d8100 p = 1) : d2185 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40177 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40412 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40414 (p : Pattern) (guard : d8106 p = 1) : d2214 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40413 p hg
    simpa only [d8106, d2214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40247 p hg
    simpa only [d8106, d2214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40415 (p : Pattern) (guard : d8107 p = 1) : d2215 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2215, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40411 p hg
    simpa only [d8107, d2215, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2215, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40414 p hg
    simpa only [d8107, d2215, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40416 (p : Pattern) (guard : d8106 p = 1) : d2218 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40413 p hg
    simpa only [d8106, d2218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40119 p hg
    simpa only [d8106, d2218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40417 (p : Pattern) (guard : d0 p = 1) : d2196 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40418 (p : Pattern) (guard : d8105 p = 1) : d2196 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40182 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40417 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40419 (p : Pattern) (guard : d8111 p = 1) : d2219 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40418 p hg
    simpa only [d8111, d2219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40420 (p : Pattern) (guard : d8112 p = 1) : d2220 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40416 p hg
    simpa only [d8112, d2220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40419 p hg
    simpa only [d8112, d2220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40421 (p : Pattern) (guard : d8113 p = 1) : d2221 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2221, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40415 p hg
    simpa only [d8113, d2221, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2221, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40420 p hg
    simpa only [d8113, d2221, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40422 (p : Pattern) (guard : d8106 p = 1) : d2222 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40413 p hg
    simpa only [d8106, d2222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40423 (p : Pattern) (guard : d8112 p = 1) : d2223 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40422 p hg
    simpa only [d8112, d2223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40419 p hg
    simpa only [d8112, d2223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40424 (p : Pattern) (guard : d8117 p = 1) : d2225 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40217 p hg
    simpa only [d8117, d2225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40425 (p : Pattern) (guard : d8118 p = 1) : d2226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40423 p hg
    simpa only [d8118, d2226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40424 p hg
    simpa only [d8118, d2226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40426 (p : Pattern) (guard : d8119 p = 1) : d2227 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2227, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40421 p hg
    simpa only [d8119, d2227, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2227, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40425 p hg
    simpa only [d8119, d2227, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40427 (p : Pattern) (guard : d8120 p = 1) : d2312 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2312, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40410 p hg
    simpa only [d8120, d2312, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2312, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40426 p hg
    simpa only [d8120, d2312, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40428 (p : Pattern) (guard : d8090 p = 1) : d2185 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34875 p hg
    simpa only [d8090, d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40429 (p : Pattern) (guard : d8095 p = 1) : d2185 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40428 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40177 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40430 (p : Pattern) (guard : d8101 p = 1) : d2201 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2201, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40429 p hg
    simpa only [d8101, d2201, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2201, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40232 p hg
    simpa only [d8101, d2201, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40431 (p : Pattern) (guard : d8094 p = 1) : d2209 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2209, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34881 p hg
    simpa only [d8094, d2209, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2209, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2209, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40432 (p : Pattern) (guard : d8100 p = 1) : d2209 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40431 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40211 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40433 (p : Pattern) (guard : d8106 p = 1) : d2232 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2232, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40432 p hg
    simpa only [d8106, d2232, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2232, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40256 p hg
    simpa only [d8106, d2232, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40434 (p : Pattern) (guard : d8107 p = 1) : d2263 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2263, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40430 p hg
    simpa only [d8107, d2263, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2263, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40433 p hg
    simpa only [d8107, d2263, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40435 (p : Pattern) (guard : d8094 p = 1) : d2196 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2196, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34887 p hg
    simpa only [d8094, d2196, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2196, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2196, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40436 (p : Pattern) (guard : d8100 p = 1) : d2196 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40435 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40182 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40437 (p : Pattern) (guard : d8106 p = 1) : d2198 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2198, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40436 p hg
    simpa only [d8106, d2198, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2198, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40236 p hg
    simpa only [d8106, d2198, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40438 (p : Pattern) (guard : d8112 p = 1) : d2234 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2234, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40437 p hg
    simpa only [d8112, d2234, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2234, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40260 p hg
    simpa only [d8112, d2234, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40439 (p : Pattern) (guard : d8113 p = 1) : d2264 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2264, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40434 p hg
    simpa only [d8113, d2264, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2264, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40438 p hg
    simpa only [d8113, d2264, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40440 (p : Pattern) (guard : d8112 p = 1) : d2239 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2239, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40390 p hg
    simpa only [d8112, d2239, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2239, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40264 p hg
    simpa only [d8112, d2239, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40441 (p : Pattern) (guard : d8118 p = 1) : d2242 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2242, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40440 p hg
    simpa only [d8118, d2242, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2242, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40268 p hg
    simpa only [d8118, d2242, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40442 (p : Pattern) (guard : d8119 p = 1) : d2265 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2265, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40439 p hg
    simpa only [d8119, d2265, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2265, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40441 p hg
    simpa only [d8119, d2265, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40443 (p : Pattern) (guard : d0 p = 1) : d2209 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40444 (p : Pattern) (guard : d8105 p = 1) : d2209 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40211 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40443 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40445 (p : Pattern) (guard : d8111 p = 1) : d2244 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40444 p hg
    simpa only [d8111, d2244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40446 (p : Pattern) (guard : d8112 p = 1) : d2245 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40414 p hg
    simpa only [d8112, d2245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40445 p hg
    simpa only [d8112, d2245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40447 (p : Pattern) (guard : d0 p = 1) : d2224 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40448 (p : Pattern) (guard : d8117 p = 1) : d2246 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40419 p hg
    simpa only [d8117, d2246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40447 p hg
    simpa only [d8117, d2246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40449 (p : Pattern) (guard : d8118 p = 1) : d2247 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40446 p hg
    simpa only [d8118, d2247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40448 p hg
    simpa only [d8118, d2247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40450 (p : Pattern) (guard : d0 p = 1) : d2248 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40451 (p : Pattern) (guard : d8117 p = 1) : d2249 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40419 p hg
    simpa only [d8117, d2249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40450 p hg
    simpa only [d8117, d2249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40452 (p : Pattern) (guard : d0 p = 1) : d2251 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40453 (p : Pattern) (guard : d8123 p = 1) : d2252 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40451 p hg
    simpa only [d8123, d2252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40452 p hg
    simpa only [d8123, d2252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40454 (p : Pattern) (guard : d8124 p = 1) : d2253 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40449 p hg
    simpa only [d8124, d2253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40453 p hg
    simpa only [d8124, d2253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40455 (p : Pattern) (guard : d8125 p = 1) : d2291 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2291, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40442 p hg
    simpa only [d8125, d2291, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2291, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40454 p hg
    simpa only [d8125, d2291, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40456 (p : Pattern) (guard : d8126 p = 1) : d2313 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2313, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40427 p hg
    simpa only [d8126, d2313, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2313, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40455 p hg
    simpa only [d8126, d2313, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40457 (p : Pattern) (guard : d8105 p = 1) : d2187 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40412 p hg
    simpa only [d8105, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40458 (p : Pattern) (guard : d8106 p = 1) : d2201 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40413 p hg
    simpa only [d8106, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40457 p hg
    simpa only [d8106, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40459 (p : Pattern) (guard : d8107 p = 1) : d2201 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40284 p hg
    simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40458 p hg
    simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
