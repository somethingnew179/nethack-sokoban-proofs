/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons285
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare40040 (p : Pattern) (guard : d8090 p = 1) : d2216 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2216, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34508 p hg
    simpa only [d8090, d2216, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2216, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2216, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40041 (p : Pattern) (guard : d8094 p = 1) : d2216 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34436 p hg
    simpa only [d8094, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40042 (p : Pattern) (guard : d8095 p = 1) : d2216 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40040 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40041 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40043 (p : Pattern) (guard : d8100 p = 1) : d2217 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40041 p hg
    simpa only [d8100, d2217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40044 (p : Pattern) (guard : d8101 p = 1) : d2240 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2240, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40042 p hg
    simpa only [d8101, d2240, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2240, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40043 p hg
    simpa only [d8101, d2240, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40045 (p : Pattern) (guard : d8107 p = 1) : d2241 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2241, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40044 p hg
    simpa only [d8107, d2241, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2241, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2241, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40046 (p : Pattern) (guard : d8108 p = 1) : d2242 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2242, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40039 p hg
    simpa only [d8108, d2242, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2242, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40045 p hg
    simpa only [d8108, d2242, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40047 (p : Pattern) (guard : d8109 p = 1) : d2243 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2243, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40033 p hg
    simpa only [d8109, d2243, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2243, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40046 p hg
    simpa only [d8109, d2243, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40048 (p : Pattern) (guard : d8086 p = 1) : d2185 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34324 p hg
    simpa only [d8086, d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40049 (p : Pattern) (guard : d8091 p = 1) : d2185 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40048 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39988 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40050 (p : Pattern) (guard : d8096 p = 1) : d2214 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2214, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40049 p hg
    simpa only [d8096, d2214, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2214, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39991 p hg
    simpa only [d8096, d2214, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40051 (p : Pattern) (guard : d8090 p = 1) : d2209 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34523 p hg
    simpa only [d8090, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40052 (p : Pattern) (guard : d8094 p = 1) : d2209 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34473 p hg
    simpa only [d8094, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40053 (p : Pattern) (guard : d8095 p = 1) : d2209 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40051 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40052 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40054 (p : Pattern) (guard : d8101 p = 1) : d2244 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2244, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40053 p hg
    simpa only [d8101, d2244, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2244, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d2244, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40055 (p : Pattern) (guard : d8102 p = 1) : d2245 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2245, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40050 p hg
    simpa only [d8102, d2245, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2245, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40054 p hg
    simpa only [d8102, d2245, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40056 (p : Pattern) (guard : d8099 p = 1) : d2203 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34451 p hg
    simpa only [d8099, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40057 (p : Pattern) (guard : d8100 p = 1) : d2203 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40007 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40056 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40058 (p : Pattern) (guard : d8106 p = 1) : d2224 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40057 p hg
    simpa only [d8106, d2224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40059 (p : Pattern) (guard : d8107 p = 1) : d2246 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40001 p hg
    simpa only [d8107, d2246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40058 p hg
    simpa only [d8107, d2246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40060 (p : Pattern) (guard : d8108 p = 1) : d2247 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2247, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40055 p hg
    simpa only [d8108, d2247, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2247, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40059 p hg
    simpa only [d8108, d2247, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40061 (p : Pattern) (guard : d8099 p = 1) : d2236 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34501 p hg
    simpa only [d8099, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40062 (p : Pattern) (guard : d8100 p = 1) : d2236 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40035 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40061 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40063 (p : Pattern) (guard : d8106 p = 1) : d2248 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40062 p hg
    simpa only [d8106, d2248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40064 (p : Pattern) (guard : d8107 p = 1) : d2249 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40001 p hg
    simpa only [d8107, d2249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40063 p hg
    simpa only [d8107, d2249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40065 (p : Pattern) (guard : d8099 p = 1) : d2216 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34510 p hg
    simpa only [d8099, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40066 (p : Pattern) (guard : d8100 p = 1) : d2216 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40041 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40065 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40067 (p : Pattern) (guard : d8106 p = 1) : d2250 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40066 p hg
    simpa only [d8106, d2250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40068 (p : Pattern) (guard : d8112 p = 1) : d2251 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40067 p hg
    simpa only [d8112, d2251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40069 (p : Pattern) (guard : d8113 p = 1) : d2252 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40064 p hg
    simpa only [d8113, d2252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40068 p hg
    simpa only [d8113, d2252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40070 (p : Pattern) (guard : d8114 p = 1) : d2253 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2253, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40060 p hg
    simpa only [d8114, d2253, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2253, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40069 p hg
    simpa only [d8114, d2253, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40071 (p : Pattern) (guard : d8115 p = 1) : d2254 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2254, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40047 p hg
    simpa only [d8115, d2254, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2254, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40070 p hg
    simpa only [d8115, d2254, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40072 (p : Pattern) (guard : d8116 p = 1) : d2255 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8110 p = 1 := by simpa only [d8116, d2255, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40013 p hg
    simpa only [d8116, d2255, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8115 p = 1 := by simpa only [d8116, d2255, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40071 p hg
    simpa only [d8116, d2255, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40073 (p : Pattern) (guard : d8095 p = 1) : d2187 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39988 p hg
    simpa only [d8095, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40074 (p : Pattern) (guard : d8096 p = 1) : d2201 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2201, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40049 p hg
    simpa only [d8096, d2201, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2201, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40073 p hg
    simpa only [d8096, d2201, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40075 (p : Pattern) (guard : d8097 p = 1) : d2201 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39969 p hg
    simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40074 p hg
    simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40076 (p : Pattern) (guard : d8096 p = 1) : d2201 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39989 p hg
    simpa only [d8096, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40073 p hg
    simpa only [d8096, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40077 (p : Pattern) (guard : d8100 p = 1) : d2197 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39999 p hg
    simpa only [d8100, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40078 (p : Pattern) (guard : d8101 p = 1) : d2198 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40000 p hg
    simpa only [d8101, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40077 p hg
    simpa only [d8101, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40079 (p : Pattern) (guard : d8102 p = 1) : d2202 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2202, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40076 p hg
    simpa only [d8102, d2202, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2202, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40078 p hg
    simpa only [d8102, d2202, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40080 (p : Pattern) (guard : d8103 p = 1) : d2256 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2256, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40075 p hg
    simpa only [d8103, d2256, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2256, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40079 p hg
    simpa only [d8103, d2256, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40081 (p : Pattern) (guard : d8096 p = 1) : d2201 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39994 p hg
    simpa only [d8096, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40073 p hg
    simpa only [d8096, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40082 (p : Pattern) (guard : d8102 p = 1) : d2202 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2202, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40081 p hg
    simpa only [d8102, d2202, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2202, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40078 p hg
    simpa only [d8102, d2202, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40083 (p : Pattern) (guard : d8101 p = 1) : d2205 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40008 p hg
    simpa only [d8101, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40030 p hg
    simpa only [d8101, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40084 (p : Pattern) (guard : d8107 p = 1) : d2206 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40083 p hg
    simpa only [d8107, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40085 (p : Pattern) (guard : d8108 p = 1) : d2207 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2207, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40082 p hg
    simpa only [d8108, d2207, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2207, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40084 p hg
    simpa only [d8108, d2207, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40086 (p : Pattern) (guard : d8109 p = 1) : d2257 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2257, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40080 p hg
    simpa only [d8109, d2257, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2257, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40085 p hg
    simpa only [d8109, d2257, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40087 (p : Pattern) (guard : d8086 p = 1) : d2209 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34563 p hg
    simpa only [d8086, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2209, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40088 (p : Pattern) (guard : d8091 p = 1) : d2209 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40087 p hg
    simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40020 p hg
    simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40089 (p : Pattern) (guard : d8096 p = 1) : d2232 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40088 p hg
    simpa only [d8096, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40022 p hg
    simpa only [d8096, d2232, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40090 (p : Pattern) (guard : d8094 p = 1) : d2212 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34425 p hg
    simpa only [d8094, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40091 (p : Pattern) (guard : d8095 p = 1) : d2212 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39990 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40090 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40092 (p : Pattern) (guard : d8100 p = 1) : d2213 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40090 p hg
    simpa only [d8100, d2213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40093 (p : Pattern) (guard : d8101 p = 1) : d2258 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40091 p hg
    simpa only [d8101, d2258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40092 p hg
    simpa only [d8101, d2258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40094 (p : Pattern) (guard : d8102 p = 1) : d2259 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2259, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40089 p hg
    simpa only [d8102, d2259, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2259, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40093 p hg
    simpa only [d8102, d2259, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40095 (p : Pattern) (guard : d8095 p = 1) : d2216 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39995 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40041 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40096 (p : Pattern) (guard : d8101 p = 1) : d2240 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40095 p hg
    simpa only [d8101, d2240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40043 p hg
    simpa only [d8101, d2240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40097 (p : Pattern) (guard : d8107 p = 1) : d2241 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40096 p hg
    simpa only [d8107, d2241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40098 (p : Pattern) (guard : d8108 p = 1) : d2260 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2260, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40094 p hg
    simpa only [d8108, d2260, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2260, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40097 p hg
    simpa only [d8108, d2260, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40099 (p : Pattern) (guard : d8114 p = 1) : d2261 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2261, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40098 p hg
    simpa only [d8114, d2261, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2261, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d2261, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40100 (p : Pattern) (guard : d8115 p = 1) : d2262 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2262, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40086 p hg
    simpa only [d8115, d2262, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2262, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40099 p hg
    simpa only [d8115, d2262, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40101 (p : Pattern) (guard : d8086 p = 1) : d2185 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34322 p hg
    simpa only [d8086, d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40102 (p : Pattern) (guard : d8091 p = 1) : d2185 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40101 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39988 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40103 (p : Pattern) (guard : d8096 p = 1) : d2201 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2201, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40102 p hg
    simpa only [d8096, d2201, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2201, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40073 p hg
    simpa only [d8096, d2201, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40104 (p : Pattern) (guard : d8090 p = 1) : d2209 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34586 p hg
    simpa only [d8090, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40105 (p : Pattern) (guard : d8095 p = 1) : d2209 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40104 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40052 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40106 (p : Pattern) (guard : d8100 p = 1) : d2210 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40052 p hg
    simpa only [d8100, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40107 (p : Pattern) (guard : d8101 p = 1) : d2232 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40105 p hg
    simpa only [d8101, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40106 p hg
    simpa only [d8101, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40108 (p : Pattern) (guard : d8102 p = 1) : d2263 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2263, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40103 p hg
    simpa only [d8102, d2263, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2263, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40107 p hg
    simpa only [d8102, d2263, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40109 (p : Pattern) (guard : d8090 p = 1) : d2196 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2196, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34594 p hg
    simpa only [d8090, d2196, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2196, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2196, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40110 (p : Pattern) (guard : d8095 p = 1) : d2196 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40109 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39999 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40111 (p : Pattern) (guard : d8101 p = 1) : d2198 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2198, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40110 p hg
    simpa only [d8101, d2198, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2198, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40077 p hg
    simpa only [d8101, d2198, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40112 (p : Pattern) (guard : d8105 p = 1) : d2204 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40056 p hg
    simpa only [d8105, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40113 (p : Pattern) (guard : d8106 p = 1) : d2205 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40057 p hg
    simpa only [d8106, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40112 p hg
    simpa only [d8106, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40114 (p : Pattern) (guard : d8107 p = 1) : d2234 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2234, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40111 p hg
    simpa only [d8107, d2234, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2234, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40113 p hg
    simpa only [d8107, d2234, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40115 (p : Pattern) (guard : d8108 p = 1) : d2264 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2264, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40108 p hg
    simpa only [d8108, d2264, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2264, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40114 p hg
    simpa only [d8108, d2264, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40116 (p : Pattern) (guard : d8105 p = 1) : d2237 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40061 p hg
    simpa only [d8105, d2237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40117 (p : Pattern) (guard : d8106 p = 1) : d2238 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40062 p hg
    simpa only [d8106, d2238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40116 p hg
    simpa only [d8106, d2238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40118 (p : Pattern) (guard : d8107 p = 1) : d2239 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40078 p hg
    simpa only [d8107, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40117 p hg
    simpa only [d8107, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40119 (p : Pattern) (guard : d8105 p = 1) : d2217 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40065 p hg
    simpa only [d8105, d2217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40120 (p : Pattern) (guard : d8106 p = 1) : d2240 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40066 p hg
    simpa only [d8106, d2240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40119 p hg
    simpa only [d8106, d2240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40121 (p : Pattern) (guard : d8112 p = 1) : d2241 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40120 p hg
    simpa only [d8112, d2241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40122 (p : Pattern) (guard : d8113 p = 1) : d2242 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40118 p hg
    simpa only [d8113, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40121 p hg
    simpa only [d8113, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40123 (p : Pattern) (guard : d8114 p = 1) : d2265 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2265, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40115 p hg
    simpa only [d8114, d2265, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2265, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40122 p hg
    simpa only [d8114, d2265, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40124 (p : Pattern) (guard : d8107 p = 1) : d2266 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40093 p hg
    simpa only [d8107, d2266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40125 (p : Pattern) (guard : d8113 p = 1) : d2267 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40124 p hg
    simpa only [d8113, d2267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d2267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40126 (p : Pattern) (guard : d8119 p = 1) : d2268 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40125 p hg
    simpa only [d8119, d2268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40127 (p : Pattern) (guard : d8120 p = 1) : d2269 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2269, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40123 p hg
    simpa only [d8120, d2269, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2269, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40126 p hg
    simpa only [d8120, d2269, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40128 (p : Pattern) (guard : d8121 p = 1) : d2270 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d2270, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40100 p hg
    simpa only [d8121, d2270, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d2270, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40127 p hg
    simpa only [d8121, d2270, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40129 (p : Pattern) (guard : d8122 p = 1) : d2271 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d2271, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40072 p hg
    simpa only [d8122, d2271, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d2271, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40128 p hg
    simpa only [d8122, d2271, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40130 (p : Pattern) (guard : d8097 p = 1) : d2272 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2272, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39957 p hg
    simpa only [d8097, d2272, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2272, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40103 p hg
    simpa only [d8097, d2272, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40131 (p : Pattern) (guard : d8102 p = 1) : d2202 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2202, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40074 p hg
    simpa only [d8102, d2202, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2202, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40111 p hg
    simpa only [d8102, d2202, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40132 (p : Pattern) (guard : d8103 p = 1) : d2273 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2273, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40130 p hg
    simpa only [d8103, d2273, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2273, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40131 p hg
    simpa only [d8103, d2273, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40133 (p : Pattern) (guard : d8108 p = 1) : d2207 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2207, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40079 p hg
    simpa only [d8108, d2207, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2207, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40084 p hg
    simpa only [d8108, d2207, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40134 (p : Pattern) (guard : d8109 p = 1) : d2274 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2274, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40132 p hg
    simpa only [d8109, d2274, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2274, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40133 p hg
    simpa only [d8109, d2274, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40135 (p : Pattern) (guard : d8086 p = 1) : d2209 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38107 p hg
    simpa only [d8086, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2209, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40136 (p : Pattern) (guard : d8091 p = 1) : d2209 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40135 p hg
    simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40020 p hg
    simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40137 (p : Pattern) (guard : d8096 p = 1) : d2232 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40136 p hg
    simpa only [d8096, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40022 p hg
    simpa only [d8096, d2232, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40138 (p : Pattern) (guard : d8102 p = 1) : d2259 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2259, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40137 p hg
    simpa only [d8102, d2259, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2259, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40093 p hg
    simpa only [d8102, d2259, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40139 (p : Pattern) (guard : d8108 p = 1) : d2260 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2260, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40138 p hg
    simpa only [d8108, d2260, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2260, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40097 p hg
    simpa only [d8108, d2260, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40140 (p : Pattern) (guard : d8114 p = 1) : d2261 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2261, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40139 p hg
    simpa only [d8114, d2261, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2261, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d2261, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40141 (p : Pattern) (guard : d8115 p = 1) : d2275 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2275, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40134 p hg
    simpa only [d8115, d2275, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2275, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40140 p hg
    simpa only [d8115, d2275, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40142 (p : Pattern) (guard : d8086 p = 1) : d2185 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34404 p hg
    simpa only [d8086, d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40143 (p : Pattern) (guard : d8091 p = 1) : d2185 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40142 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39988 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40144 (p : Pattern) (guard : d8096 p = 1) : d2201 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2201, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40143 p hg
    simpa only [d8096, d2201, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2201, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40073 p hg
    simpa only [d8096, d2201, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40145 (p : Pattern) (guard : d8090 p = 1) : d2209 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2209, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38599 p hg
    simpa only [d8090, d2209, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2209, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2209, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40146 (p : Pattern) (guard : d8095 p = 1) : d2209 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40145 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40052 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40147 (p : Pattern) (guard : d8101 p = 1) : d2232 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2232, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40146 p hg
    simpa only [d8101, d2232, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2232, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40106 p hg
    simpa only [d8101, d2232, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40148 (p : Pattern) (guard : d8102 p = 1) : d2263 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2263, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40144 p hg
    simpa only [d8102, d2263, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2263, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40147 p hg
    simpa only [d8102, d2263, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40149 (p : Pattern) (guard : d8090 p = 1) : d2196 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2196, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34626 p hg
    simpa only [d8090, d2196, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2196, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2196, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40150 (p : Pattern) (guard : d8095 p = 1) : d2196 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40149 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39999 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40151 (p : Pattern) (guard : d8101 p = 1) : d2198 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2198, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40150 p hg
    simpa only [d8101, d2198, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2198, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40077 p hg
    simpa only [d8101, d2198, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40152 (p : Pattern) (guard : d8107 p = 1) : d2234 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2234, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40151 p hg
    simpa only [d8107, d2234, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2234, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40113 p hg
    simpa only [d8107, d2234, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40153 (p : Pattern) (guard : d8108 p = 1) : d2264 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2264, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40148 p hg
    simpa only [d8108, d2264, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2264, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40152 p hg
    simpa only [d8108, d2264, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40154 (p : Pattern) (guard : d8107 p = 1) : d2239 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2239, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40111 p hg
    simpa only [d8107, d2239, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2239, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40117 p hg
    simpa only [d8107, d2239, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40155 (p : Pattern) (guard : d8113 p = 1) : d2242 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2242, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40154 p hg
    simpa only [d8113, d2242, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2242, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40121 p hg
    simpa only [d8113, d2242, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40156 (p : Pattern) (guard : d8114 p = 1) : d2265 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2265, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40153 p hg
    simpa only [d8114, d2265, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2265, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40155 p hg
    simpa only [d8114, d2265, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40157 (p : Pattern) (guard : d8120 p = 1) : d2269 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2269, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40156 p hg
    simpa only [d8120, d2269, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2269, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40126 p hg
    simpa only [d8120, d2269, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40158 (p : Pattern) (guard : d8121 p = 1) : d2276 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d2276, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40141 p hg
    simpa only [d8121, d2276, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d2276, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40157 p hg
    simpa only [d8121, d2276, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40159 (p : Pattern) (guard : d8102 p = 1) : d2277 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2277, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39978 p hg
    simpa only [d8102, d2277, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2277, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40096 p hg
    simpa only [d8102, d2277, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40160 (p : Pattern) (guard : d8108 p = 1) : d2278 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2278, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40159 p hg
    simpa only [d8108, d2278, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2278, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40097 p hg
    simpa only [d8108, d2278, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40161 (p : Pattern) (guard : d8113 p = 1) : d2279 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40097 p hg
    simpa only [d8113, d2279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d2279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40162 (p : Pattern) (guard : d8114 p = 1) : d2280 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2280, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40160 p hg
    simpa only [d8114, d2280, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2280, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40161 p hg
    simpa only [d8114, d2280, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40163 (p : Pattern) (guard : d8119 p = 1) : d2281 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40161 p hg
    simpa only [d8119, d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40164 (p : Pattern) (guard : d8120 p = 1) : d2282 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2282, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40162 p hg
    simpa only [d8120, d2282, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2282, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40163 p hg
    simpa only [d8120, d2282, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40165 (p : Pattern) (guard : d8113 p = 1) : d2279 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2279, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40045 p hg
    simpa only [d8113, d2279, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2279, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d2279, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40166 (p : Pattern) (guard : d8119 p = 1) : d2281 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2281, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40165 p hg
    simpa only [d8119, d2281, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2281, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2281, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40167 (p : Pattern) (guard : d8125 p = 1) : d2283 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2283, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40166 p hg
    simpa only [d8125, d2283, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2283, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d2283, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40168 (p : Pattern) (guard : d8126 p = 1) : d2284 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2284, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40164 p hg
    simpa only [d8126, d2284, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2284, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40167 p hg
    simpa only [d8126, d2284, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40169 (p : Pattern) (guard : d8127 p = 1) : d2285 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d2285, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40158 p hg
    simpa only [d8127, d2285, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d2285, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40168 p hg
    simpa only [d8127, d2285, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40170 (p : Pattern) (guard : d8128 p = 1) : d2286 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d2286, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40129 p hg
    simpa only [d8128, d2286, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d2286, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40169 p hg
    simpa only [d8128, d2286, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40171 (p : Pattern) (guard : d8097 p = 1) : d2287 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2287, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39950 p hg
    simpa only [d8097, d2287, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2287, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40144 p hg
    simpa only [d8097, d2287, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40172 (p : Pattern) (guard : d8102 p = 1) : d2202 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2202, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40103 p hg
    simpa only [d8102, d2202, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2202, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40151 p hg
    simpa only [d8102, d2202, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40173 (p : Pattern) (guard : d8103 p = 1) : d2288 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2288, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40171 p hg
    simpa only [d8103, d2288, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2288, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40172 p hg
    simpa only [d8103, d2288, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40174 (p : Pattern) (guard : d8108 p = 1) : d2207 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2207, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40131 p hg
    simpa only [d8108, d2207, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2207, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40084 p hg
    simpa only [d8108, d2207, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40175 (p : Pattern) (guard : d8109 p = 1) : d2289 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2289, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40173 p hg
    simpa only [d8109, d2289, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2289, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40174 p hg
    simpa only [d8109, d2289, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40176 (p : Pattern) (guard : d8096 p = 1) : d2211 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2211, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39989 p hg
    simpa only [d8096, d2211, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2211, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40022 p hg
    simpa only [d8096, d2211, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40177 (p : Pattern) (guard : d8094 p = 1) : d2185 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34417 p hg
    simpa only [d8094, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40178 (p : Pattern) (guard : d8095 p = 1) : d2185 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39988 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40177 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40179 (p : Pattern) (guard : d8101 p = 1) : d2214 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40178 p hg
    simpa only [d8101, d2214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40092 p hg
    simpa only [d8101, d2214, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
