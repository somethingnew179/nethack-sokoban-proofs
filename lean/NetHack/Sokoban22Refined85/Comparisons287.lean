/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons286
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare40180 (p : Pattern) (guard : d8102 p = 1) : d2215 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2215, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40176 p hg
    simpa only [d8102, d2215, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2215, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40179 p hg
    simpa only [d8102, d2215, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40181 (p : Pattern) (guard : d8101 p = 1) : d2218 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40178 p hg
    simpa only [d8101, d2218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40043 p hg
    simpa only [d8101, d2218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40182 (p : Pattern) (guard : d8099 p = 1) : d2196 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34440 p hg
    simpa only [d8099, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40183 (p : Pattern) (guard : d8100 p = 1) : d2196 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39999 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40182 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40184 (p : Pattern) (guard : d8106 p = 1) : d2219 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40183 p hg
    simpa only [d8106, d2219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40185 (p : Pattern) (guard : d8107 p = 1) : d2220 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40181 p hg
    simpa only [d8107, d2220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40184 p hg
    simpa only [d8107, d2220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40186 (p : Pattern) (guard : d8108 p = 1) : d2221 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2221, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40180 p hg
    simpa only [d8108, d2221, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2221, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40185 p hg
    simpa only [d8108, d2221, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40187 (p : Pattern) (guard : d8101 p = 1) : d2222 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40178 p hg
    simpa only [d8101, d2222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d2222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40188 (p : Pattern) (guard : d8107 p = 1) : d2223 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40187 p hg
    simpa only [d8107, d2223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40184 p hg
    simpa only [d8107, d2223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40189 (p : Pattern) (guard : d8112 p = 1) : d2225 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40058 p hg
    simpa only [d8112, d2225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40190 (p : Pattern) (guard : d8113 p = 1) : d2226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40188 p hg
    simpa only [d8113, d2226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40189 p hg
    simpa only [d8113, d2226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40191 (p : Pattern) (guard : d8114 p = 1) : d2227 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2227, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40186 p hg
    simpa only [d8114, d2227, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2227, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40190 p hg
    simpa only [d8114, d2227, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40192 (p : Pattern) (guard : d8115 p = 1) : d2290 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2290, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40175 p hg
    simpa only [d8115, d2290, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2290, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40191 p hg
    simpa only [d8115, d2290, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40193 (p : Pattern) (guard : d8086 p = 1) : d2185 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34373 p hg
    simpa only [d8086, d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40194 (p : Pattern) (guard : d8091 p = 1) : d2185 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40193 p hg
    simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39988 p hg
    simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40195 (p : Pattern) (guard : d8096 p = 1) : d2201 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40194 p hg
    simpa only [d8096, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40073 p hg
    simpa only [d8096, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40196 (p : Pattern) (guard : d8090 p = 1) : d2209 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2209, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34658 p hg
    simpa only [d8090, d2209, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2209, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2209, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40197 (p : Pattern) (guard : d8095 p = 1) : d2209 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40196 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40052 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40198 (p : Pattern) (guard : d8101 p = 1) : d2232 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2232, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40197 p hg
    simpa only [d8101, d2232, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2232, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40106 p hg
    simpa only [d8101, d2232, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40199 (p : Pattern) (guard : d8102 p = 1) : d2263 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2263, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40195 p hg
    simpa only [d8102, d2263, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2263, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40198 p hg
    simpa only [d8102, d2263, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40200 (p : Pattern) (guard : d8090 p = 1) : d2196 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2196, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34665 p hg
    simpa only [d8090, d2196, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2196, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2196, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40201 (p : Pattern) (guard : d8095 p = 1) : d2196 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40200 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39999 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40202 (p : Pattern) (guard : d8101 p = 1) : d2198 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2198, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40201 p hg
    simpa only [d8101, d2198, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2198, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40077 p hg
    simpa only [d8101, d2198, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40203 (p : Pattern) (guard : d8107 p = 1) : d2234 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2234, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40202 p hg
    simpa only [d8107, d2234, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2234, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40113 p hg
    simpa only [d8107, d2234, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40204 (p : Pattern) (guard : d8108 p = 1) : d2264 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2264, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40199 p hg
    simpa only [d8108, d2264, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2264, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40203 p hg
    simpa only [d8108, d2264, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40205 (p : Pattern) (guard : d8107 p = 1) : d2239 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2239, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40151 p hg
    simpa only [d8107, d2239, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2239, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40117 p hg
    simpa only [d8107, d2239, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40206 (p : Pattern) (guard : d8113 p = 1) : d2242 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2242, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40205 p hg
    simpa only [d8113, d2242, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2242, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40121 p hg
    simpa only [d8113, d2242, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40207 (p : Pattern) (guard : d8114 p = 1) : d2265 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2265, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40204 p hg
    simpa only [d8114, d2265, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2265, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40206 p hg
    simpa only [d8114, d2265, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40208 (p : Pattern) (guard : d8090 p = 1) : d2185 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34674 p hg
    simpa only [d8090, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40209 (p : Pattern) (guard : d8095 p = 1) : d2185 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40208 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40177 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40210 (p : Pattern) (guard : d8101 p = 1) : d2214 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2214, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40209 p hg
    simpa only [d8101, d2214, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2214, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40092 p hg
    simpa only [d8101, d2214, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40211 (p : Pattern) (guard : d8099 p = 1) : d2209 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34525 p hg
    simpa only [d8099, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40212 (p : Pattern) (guard : d8100 p = 1) : d2209 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40052 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40211 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40213 (p : Pattern) (guard : d8106 p = 1) : d2244 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40212 p hg
    simpa only [d8106, d2244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40214 (p : Pattern) (guard : d8107 p = 1) : d2245 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2245, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40210 p hg
    simpa only [d8107, d2245, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2245, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40213 p hg
    simpa only [d8107, d2245, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40215 (p : Pattern) (guard : d0 p = 1) : d2203 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40216 (p : Pattern) (guard : d8105 p = 1) : d2203 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40056 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40215 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40217 (p : Pattern) (guard : d8111 p = 1) : d2224 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40216 p hg
    simpa only [d8111, d2224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40218 (p : Pattern) (guard : d8112 p = 1) : d2246 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40184 p hg
    simpa only [d8112, d2246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40217 p hg
    simpa only [d8112, d2246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40219 (p : Pattern) (guard : d8113 p = 1) : d2247 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2247, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40214 p hg
    simpa only [d8113, d2247, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2247, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40218 p hg
    simpa only [d8113, d2247, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40220 (p : Pattern) (guard : d0 p = 1) : d2236 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40221 (p : Pattern) (guard : d8105 p = 1) : d2236 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40061 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40220 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40222 (p : Pattern) (guard : d8111 p = 1) : d2248 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40221 p hg
    simpa only [d8111, d2248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40223 (p : Pattern) (guard : d8112 p = 1) : d2249 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40184 p hg
    simpa only [d8112, d2249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40222 p hg
    simpa only [d8112, d2249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40224 (p : Pattern) (guard : d0 p = 1) : d2216 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40225 (p : Pattern) (guard : d8105 p = 1) : d2216 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40065 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40224 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40226 (p : Pattern) (guard : d8111 p = 1) : d2250 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40225 p hg
    simpa only [d8111, d2250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40227 (p : Pattern) (guard : d8117 p = 1) : d2251 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40226 p hg
    simpa only [d8117, d2251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40228 (p : Pattern) (guard : d8118 p = 1) : d2252 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40223 p hg
    simpa only [d8118, d2252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40227 p hg
    simpa only [d8118, d2252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40229 (p : Pattern) (guard : d8119 p = 1) : d2253 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2253, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40219 p hg
    simpa only [d8119, d2253, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2253, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40228 p hg
    simpa only [d8119, d2253, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40230 (p : Pattern) (guard : d8120 p = 1) : d2291 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2291, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40207 p hg
    simpa only [d8120, d2291, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2291, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40229 p hg
    simpa only [d8120, d2291, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40231 (p : Pattern) (guard : d8121 p = 1) : d2292 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d2292, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40192 p hg
    simpa only [d8121, d2292, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d2292, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40230 p hg
    simpa only [d8121, d2292, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40232 (p : Pattern) (guard : d8100 p = 1) : d2187 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40177 p hg
    simpa only [d8100, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40233 (p : Pattern) (guard : d8101 p = 1) : d2201 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2201, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40209 p hg
    simpa only [d8101, d2201, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2201, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40232 p hg
    simpa only [d8101, d2201, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40234 (p : Pattern) (guard : d8102 p = 1) : d2201 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40074 p hg
    simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40233 p hg
    simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40235 (p : Pattern) (guard : d8101 p = 1) : d2201 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40178 p hg
    simpa only [d8101, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40232 p hg
    simpa only [d8101, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40236 (p : Pattern) (guard : d8105 p = 1) : d2197 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40182 p hg
    simpa only [d8105, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40237 (p : Pattern) (guard : d8106 p = 1) : d2198 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40183 p hg
    simpa only [d8106, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40236 p hg
    simpa only [d8106, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40238 (p : Pattern) (guard : d8107 p = 1) : d2202 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40235 p hg
    simpa only [d8107, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40237 p hg
    simpa only [d8107, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40239 (p : Pattern) (guard : d8108 p = 1) : d2256 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2256, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40234 p hg
    simpa only [d8108, d2256, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2256, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40238 p hg
    simpa only [d8108, d2256, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40240 (p : Pattern) (guard : d8112 p = 1) : d2206 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40113 p hg
    simpa only [d8112, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40241 (p : Pattern) (guard : d8113 p = 1) : d2207 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40238 p hg
    simpa only [d8113, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40240 p hg
    simpa only [d8113, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40242 (p : Pattern) (guard : d8114 p = 1) : d2257 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2257, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40239 p hg
    simpa only [d8114, d2257, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2257, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40241 p hg
    simpa only [d8114, d2257, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40243 (p : Pattern) (guard : d8095 p = 1) : d2209 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40020 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40052 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40244 (p : Pattern) (guard : d8101 p = 1) : d2232 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40243 p hg
    simpa only [d8101, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40106 p hg
    simpa only [d8101, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40245 (p : Pattern) (guard : d8099 p = 1) : d2212 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34567 p hg
    simpa only [d8099, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40246 (p : Pattern) (guard : d8100 p = 1) : d2212 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40090 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40245 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40247 (p : Pattern) (guard : d8105 p = 1) : d2213 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40245 p hg
    simpa only [d8105, d2213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40248 (p : Pattern) (guard : d8106 p = 1) : d2258 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40246 p hg
    simpa only [d8106, d2258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40247 p hg
    simpa only [d8106, d2258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40249 (p : Pattern) (guard : d8107 p = 1) : d2259 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40244 p hg
    simpa only [d8107, d2259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40248 p hg
    simpa only [d8107, d2259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40250 (p : Pattern) (guard : d8113 p = 1) : d2260 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40249 p hg
    simpa only [d8113, d2260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40121 p hg
    simpa only [d8113, d2260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40251 (p : Pattern) (guard : d8119 p = 1) : d2261 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40250 p hg
    simpa only [d8119, d2261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40252 (p : Pattern) (guard : d8120 p = 1) : d2262 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2262, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40242 p hg
    simpa only [d8120, d2262, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2262, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40251 p hg
    simpa only [d8120, d2262, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40253 (p : Pattern) (guard : d8090 p = 1) : d2185 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34717 p hg
    simpa only [d8090, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40254 (p : Pattern) (guard : d8095 p = 1) : d2185 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40253 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40177 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40255 (p : Pattern) (guard : d8101 p = 1) : d2201 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40254 p hg
    simpa only [d8101, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40232 p hg
    simpa only [d8101, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40256 (p : Pattern) (guard : d8105 p = 1) : d2210 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40211 p hg
    simpa only [d8105, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40257 (p : Pattern) (guard : d8106 p = 1) : d2232 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40212 p hg
    simpa only [d8106, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40256 p hg
    simpa only [d8106, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40258 (p : Pattern) (guard : d8107 p = 1) : d2263 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2263, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40255 p hg
    simpa only [d8107, d2263, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2263, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40257 p hg
    simpa only [d8107, d2263, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40259 (p : Pattern) (guard : d0 p = 1) : d2204 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40260 (p : Pattern) (guard : d8111 p = 1) : d2205 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40216 p hg
    simpa only [d8111, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40259 p hg
    simpa only [d8111, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40261 (p : Pattern) (guard : d8112 p = 1) : d2234 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40237 p hg
    simpa only [d8112, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40260 p hg
    simpa only [d8112, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40262 (p : Pattern) (guard : d8113 p = 1) : d2264 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2264, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40258 p hg
    simpa only [d8113, d2264, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2264, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40261 p hg
    simpa only [d8113, d2264, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40263 (p : Pattern) (guard : d0 p = 1) : d2237 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40264 (p : Pattern) (guard : d8111 p = 1) : d2238 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40221 p hg
    simpa only [d8111, d2238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40263 p hg
    simpa only [d8111, d2238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40265 (p : Pattern) (guard : d8112 p = 1) : d2239 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40237 p hg
    simpa only [d8112, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40264 p hg
    simpa only [d8112, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40266 (p : Pattern) (guard : d0 p = 1) : d2217 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40267 (p : Pattern) (guard : d8111 p = 1) : d2240 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40225 p hg
    simpa only [d8111, d2240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40266 p hg
    simpa only [d8111, d2240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40268 (p : Pattern) (guard : d8117 p = 1) : d2241 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40267 p hg
    simpa only [d8117, d2241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40269 (p : Pattern) (guard : d8118 p = 1) : d2242 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40265 p hg
    simpa only [d8118, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40268 p hg
    simpa only [d8118, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40270 (p : Pattern) (guard : d8119 p = 1) : d2265 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2265, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40262 p hg
    simpa only [d8119, d2265, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2265, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40269 p hg
    simpa only [d8119, d2265, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40271 (p : Pattern) (guard : d8112 p = 1) : d2266 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40248 p hg
    simpa only [d8112, d2266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40272 (p : Pattern) (guard : d8118 p = 1) : d2267 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40271 p hg
    simpa only [d8118, d2267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40273 (p : Pattern) (guard : d8124 p = 1) : d2268 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40272 p hg
    simpa only [d8124, d2268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40274 (p : Pattern) (guard : d8125 p = 1) : d2269 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2269, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40270 p hg
    simpa only [d8125, d2269, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2269, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40273 p hg
    simpa only [d8125, d2269, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40275 (p : Pattern) (guard : d8126 p = 1) : d2270 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2270, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40252 p hg
    simpa only [d8126, d2270, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2270, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40274 p hg
    simpa only [d8126, d2270, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40276 (p : Pattern) (guard : d8127 p = 1) : d2293 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d2293, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40231 p hg
    simpa only [d8127, d2293, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d2293, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40275 p hg
    simpa only [d8127, d2293, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40277 (p : Pattern) (guard : d8102 p = 1) : d2201 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40103 p hg
    simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40255 p hg
    simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40278 (p : Pattern) (guard : d8107 p = 1) : d2202 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2202, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40233 p hg
    simpa only [d8107, d2202, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2202, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40237 p hg
    simpa only [d8107, d2202, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40279 (p : Pattern) (guard : d8108 p = 1) : d2256 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2256, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40277 p hg
    simpa only [d8108, d2256, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2256, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40278 p hg
    simpa only [d8108, d2256, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40280 (p : Pattern) (guard : d8114 p = 1) : d2257 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2257, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40279 p hg
    simpa only [d8114, d2257, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2257, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40241 p hg
    simpa only [d8114, d2257, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40281 (p : Pattern) (guard : d8120 p = 1) : d2262 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2262, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40280 p hg
    simpa only [d8120, d2262, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2262, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40251 p hg
    simpa only [d8120, d2262, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40282 (p : Pattern) (guard : d8090 p = 1) : d2185 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34810 p hg
    simpa only [d8090, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40283 (p : Pattern) (guard : d8095 p = 1) : d2185 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40282 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40177 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40284 (p : Pattern) (guard : d8101 p = 1) : d2201 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40283 p hg
    simpa only [d8101, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40232 p hg
    simpa only [d8101, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40285 (p : Pattern) (guard : d8107 p = 1) : d2263 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2263, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40284 p hg
    simpa only [d8107, d2263, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2263, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40257 p hg
    simpa only [d8107, d2263, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40286 (p : Pattern) (guard : d8113 p = 1) : d2264 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2264, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40285 p hg
    simpa only [d8113, d2264, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2264, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40261 p hg
    simpa only [d8113, d2264, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40287 (p : Pattern) (guard : d8119 p = 1) : d2265 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2265, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40286 p hg
    simpa only [d8119, d2265, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2265, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40269 p hg
    simpa only [d8119, d2265, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40288 (p : Pattern) (guard : d8125 p = 1) : d2269 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2269, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40287 p hg
    simpa only [d8125, d2269, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2269, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40273 p hg
    simpa only [d8125, d2269, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40289 (p : Pattern) (guard : d8126 p = 1) : d2270 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2270, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40281 p hg
    simpa only [d8126, d2270, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2270, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40288 p hg
    simpa only [d8126, d2270, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40290 (p : Pattern) (guard : d8132 p = 1) : d2294 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2294, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40289 p hg
    simpa only [d8132, d2294, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2294, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d8132, d2294, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40291 (p : Pattern) (guard : d8133 p = 1) : d2295 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d2295, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40276 p hg
    simpa only [d8133, d2295, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d2295, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40290 p hg
    simpa only [d8133, d2295, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40292 (p : Pattern) (guard : d8134 p = 1) : d2296 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d2296, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40170 p hg
    simpa only [d8134, d2296, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d2296, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40291 p hg
    simpa only [d8134, d2296, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40293 (p : Pattern) (guard : d1 p = 1) : d320 p ≤ (0 : Int) + d320 p := by
  omega
theorem compare40294 (p : Pattern) (guard : d1 p = 1) : d2297 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2297, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34745 p hg
    simpa only [d2297, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2297, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40293 p hg
    simpa only [d2297, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40295 (p : Pattern) (guard : d8087 p = 1) : d2298 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2298, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40294 p hg
    simpa only [d8087, d2298, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2298, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39987 p hg
    simpa only [d8087, d2298, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40296 (p : Pattern) (guard : d8091 p = 1) : d2187 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2187, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40048 p hg
    simpa only [d8091, d2187, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2187, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2187, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40297 (p : Pattern) (guard : d8092 p = 1) : d2299 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2299, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40295 p hg
    simpa only [d8092, d2299, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2299, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40296 p hg
    simpa only [d8092, d2299, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40298 (p : Pattern) (guard : d8085 p = 1) : d332 p ≤ (0 : Int) + d332 p := by
  omega
theorem compare40299 (p : Pattern) (guard : d8086 p = 1) : d2193 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2193, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34349 p hg
    simpa only [d8086, d2193, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2193, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40298 p hg
    simpa only [d8086, d2193, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40300 (p : Pattern) (guard : d8091 p = 1) : d2194 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2194, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40299 p hg
    simpa only [d8091, d2194, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2194, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39988 p hg
    simpa only [d8091, d2194, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40301 (p : Pattern) (guard : d8095 p = 1) : d2187 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2187, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40208 p hg
    simpa only [d8095, d2187, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2187, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2187, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40302 (p : Pattern) (guard : d8096 p = 1) : d2195 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2195, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40300 p hg
    simpa only [d8096, d2195, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2195, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40301 p hg
    simpa only [d8096, d2195, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40303 (p : Pattern) (guard : d8097 p = 1) : d2300 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2300, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40297 p hg
    simpa only [d8097, d2300, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2300, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40302 p hg
    simpa only [d8097, d2300, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40304 (p : Pattern) (guard : d8090 p = 1) : d2196 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2196, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34755 p hg
    simpa only [d8090, d2196, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2196, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2196, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40305 (p : Pattern) (guard : d8095 p = 1) : d2196 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40304 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39999 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40306 (p : Pattern) (guard : d8101 p = 1) : d2198 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2198, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40305 p hg
    simpa only [d8101, d2198, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2198, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40077 p hg
    simpa only [d8101, d2198, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40307 (p : Pattern) (guard : d8102 p = 1) : d2202 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2202, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40195 p hg
    simpa only [d8102, d2202, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2202, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40306 p hg
    simpa only [d8102, d2202, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40308 (p : Pattern) (guard : d8103 p = 1) : d2301 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2301, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40303 p hg
    simpa only [d8103, d2301, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2301, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40307 p hg
    simpa only [d8103, d2301, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40309 (p : Pattern) (guard : d8102 p = 1) : d2202 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2202, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40144 p hg
    simpa only [d8102, d2202, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2202, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40202 p hg
    simpa only [d8102, d2202, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40310 (p : Pattern) (guard : d8090 p = 1) : d2203 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2203, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34764 p hg
    simpa only [d8090, d2203, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2203, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2203, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40311 (p : Pattern) (guard : d8095 p = 1) : d2203 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40310 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40007 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40312 (p : Pattern) (guard : d8101 p = 1) : d2205 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2205, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40311 p hg
    simpa only [d8101, d2205, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2205, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40030 p hg
    simpa only [d8101, d2205, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40313 (p : Pattern) (guard : d8107 p = 1) : d2206 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2206, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40312 p hg
    simpa only [d8107, d2206, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2206, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2206, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40314 (p : Pattern) (guard : d8108 p = 1) : d2207 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2207, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40309 p hg
    simpa only [d8108, d2207, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2207, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40313 p hg
    simpa only [d8108, d2207, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40315 (p : Pattern) (guard : d8109 p = 1) : d2302 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2302, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40308 p hg
    simpa only [d8109, d2302, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2302, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40314 p hg
    simpa only [d8109, d2302, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40316 (p : Pattern) (guard : d8096 p = 1) : d2211 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2211, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40102 p hg
    simpa only [d8096, d2211, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2211, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40022 p hg
    simpa only [d8096, d2211, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40317 (p : Pattern) (guard : d8101 p = 1) : d2214 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2214, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40254 p hg
    simpa only [d8101, d2214, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2214, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40092 p hg
    simpa only [d8101, d2214, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40318 (p : Pattern) (guard : d8102 p = 1) : d2215 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2215, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40316 p hg
    simpa only [d8102, d2215, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2215, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40317 p hg
    simpa only [d8102, d2215, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40319 (p : Pattern) (guard : d8101 p = 1) : d2218 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2218, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40209 p hg
    simpa only [d8101, d2218, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2218, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40043 p hg
    simpa only [d8101, d2218, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
