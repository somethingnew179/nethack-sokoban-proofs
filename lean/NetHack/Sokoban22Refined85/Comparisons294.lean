/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons293
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare41160 (p : Pattern) (guard : d8125 p = 1) : d2290 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2290, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41148 p hg
    simpa only [d8125, d2290, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2290, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41159 p hg
    simpa only [d8125, d2290, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41161 (p : Pattern) (guard : d8094 p = 1) : d2185 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35650 p hg
    simpa only [d8094, d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41162 (p : Pattern) (guard : d8100 p = 1) : d2185 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41161 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40412 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41163 (p : Pattern) (guard : d8106 p = 1) : d2201 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41162 p hg
    simpa only [d8106, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40457 p hg
    simpa only [d8106, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41164 (p : Pattern) (guard : d8099 p = 1) : d2209 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2209, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35656 p hg
    simpa only [d8099, d2209, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2209, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2209, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41165 (p : Pattern) (guard : d8105 p = 1) : d2209 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41164 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40443 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41166 (p : Pattern) (guard : d8111 p = 1) : d2232 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2232, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41165 p hg
    simpa only [d8111, d2232, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2232, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40478 p hg
    simpa only [d8111, d2232, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41167 (p : Pattern) (guard : d8112 p = 1) : d2263 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2263, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41163 p hg
    simpa only [d8112, d2263, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2263, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41166 p hg
    simpa only [d8112, d2263, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41168 (p : Pattern) (guard : d8099 p = 1) : d2196 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2196, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35663 p hg
    simpa only [d8099, d2196, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2196, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2196, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41169 (p : Pattern) (guard : d8105 p = 1) : d2196 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41168 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40417 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41170 (p : Pattern) (guard : d8111 p = 1) : d2198 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2198, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41169 p hg
    simpa only [d8111, d2198, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2198, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40460 p hg
    simpa only [d8111, d2198, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41171 (p : Pattern) (guard : d8117 p = 1) : d2234 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2234, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41170 p hg
    simpa only [d8117, d2234, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2234, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40481 p hg
    simpa only [d8117, d2234, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41172 (p : Pattern) (guard : d8118 p = 1) : d2264 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2264, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41167 p hg
    simpa only [d8118, d2264, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2264, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41171 p hg
    simpa only [d8118, d2264, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41173 (p : Pattern) (guard : d8117 p = 1) : d2239 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2239, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41023 p hg
    simpa only [d8117, d2239, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2239, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40484 p hg
    simpa only [d8117, d2239, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41174 (p : Pattern) (guard : d8123 p = 1) : d2242 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2242, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41173 p hg
    simpa only [d8123, d2242, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2242, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40486 p hg
    simpa only [d8123, d2242, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41175 (p : Pattern) (guard : d8124 p = 1) : d2265 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2265, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41172 p hg
    simpa only [d8124, d2265, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2265, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41174 p hg
    simpa only [d8124, d2265, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41176 (p : Pattern) (guard : d8111 p = 1) : d2214 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2214, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41063 p hg
    simpa only [d8111, d2214, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2214, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40469 p hg
    simpa only [d8111, d2214, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41177 (p : Pattern) (guard : d0 p = 1) : d2244 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41178 (p : Pattern) (guard : d8117 p = 1) : d2245 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2245, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41176 p hg
    simpa only [d8117, d2245, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2245, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41177 p hg
    simpa only [d8117, d2245, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41179 (p : Pattern) (guard : d0 p = 1) : d2246 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41180 (p : Pattern) (guard : d8123 p = 1) : d2247 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2247, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41178 p hg
    simpa only [d8123, d2247, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2247, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41179 p hg
    simpa only [d8123, d2247, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41181 (p : Pattern) (guard : d0 p = 1) : d2252 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41182 (p : Pattern) (guard : d8129 p = 1) : d2253 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2253, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41180 p hg
    simpa only [d8129, d2253, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2253, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41181 p hg
    simpa only [d8129, d2253, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41183 (p : Pattern) (guard : d8130 p = 1) : d2291 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2291, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41175 p hg
    simpa only [d8130, d2291, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2291, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41182 p hg
    simpa only [d8130, d2291, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41184 (p : Pattern) (guard : d8131 p = 1) : d2292 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2292, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41160 p hg
    simpa only [d8131, d2292, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2292, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41183 p hg
    simpa only [d8131, d2292, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41185 (p : Pattern) (guard : d0 p = 1) : d2198 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41186 (p : Pattern) (guard : d8117 p = 1) : d2202 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41040 p hg
    simpa only [d8117, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41185 p hg
    simpa only [d8117, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41187 (p : Pattern) (guard : d8118 p = 1) : d2256 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2256, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41065 p hg
    simpa only [d8118, d2256, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2256, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41186 p hg
    simpa only [d8118, d2256, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41188 (p : Pattern) (guard : d0 p = 1) : d2206 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41189 (p : Pattern) (guard : d8123 p = 1) : d2207 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41186 p hg
    simpa only [d8123, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41188 p hg
    simpa only [d8123, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41190 (p : Pattern) (guard : d8124 p = 1) : d2257 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2257, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41187 p hg
    simpa only [d8124, d2257, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2257, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41189 p hg
    simpa only [d8124, d2257, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41191 (p : Pattern) (guard : d8129 p = 1) : d2261 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41045 p hg
    simpa only [d8129, d2261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41192 (p : Pattern) (guard : d8130 p = 1) : d2262 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2262, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41190 p hg
    simpa only [d8130, d2262, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2262, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41191 p hg
    simpa only [d8130, d2262, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41193 (p : Pattern) (guard : d8099 p = 1) : d2185 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35683 p hg
    simpa only [d8099, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41194 (p : Pattern) (guard : d8105 p = 1) : d2185 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41193 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41037 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41195 (p : Pattern) (guard : d8111 p = 1) : d2201 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41194 p hg
    simpa only [d8111, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41039 p hg
    simpa only [d8111, d2201, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41196 (p : Pattern) (guard : d8117 p = 1) : d2263 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2263, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41195 p hg
    simpa only [d8117, d2263, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2263, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41052 p hg
    simpa only [d8117, d2263, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41197 (p : Pattern) (guard : d0 p = 1) : d2234 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41198 (p : Pattern) (guard : d8123 p = 1) : d2264 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2264, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41196 p hg
    simpa only [d8123, d2264, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2264, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41197 p hg
    simpa only [d8123, d2264, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41199 (p : Pattern) (guard : d0 p = 1) : d2242 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41200 (p : Pattern) (guard : d8129 p = 1) : d2265 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2265, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41198 p hg
    simpa only [d8129, d2265, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2265, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41199 p hg
    simpa only [d8129, d2265, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41201 (p : Pattern) (guard : d0 p = 1) : d2268 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41202 (p : Pattern) (guard : d8135 p = 1) : d2269 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2269, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41200 p hg
    simpa only [d8135, d2269, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2269, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41201 p hg
    simpa only [d8135, d2269, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41203 (p : Pattern) (guard : d8136 p = 1) : d2270 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2270, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41192 p hg
    simpa only [d8136, d2270, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2270, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41202 p hg
    simpa only [d8136, d2270, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41204 (p : Pattern) (guard : d8137 p = 1) : d2293 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2293, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41184 p hg
    simpa only [d8137, d2293, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2293, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41203 p hg
    simpa only [d8137, d2293, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41205 (p : Pattern) (guard : d8112 p = 1) : d2201 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40976 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41195 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41206 (p : Pattern) (guard : d8117 p = 1) : d2202 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2202, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41064 p hg
    simpa only [d8117, d2202, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2202, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41185 p hg
    simpa only [d8117, d2202, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41207 (p : Pattern) (guard : d8118 p = 1) : d2256 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2256, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41205 p hg
    simpa only [d8118, d2256, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2256, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41206 p hg
    simpa only [d8118, d2256, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41208 (p : Pattern) (guard : d8124 p = 1) : d2257 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2257, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41207 p hg
    simpa only [d8124, d2257, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2257, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41189 p hg
    simpa only [d8124, d2257, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41209 (p : Pattern) (guard : d8130 p = 1) : d2262 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2262, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41208 p hg
    simpa only [d8130, d2262, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2262, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41191 p hg
    simpa only [d8130, d2262, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41210 (p : Pattern) (guard : d8099 p = 1) : d2185 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39764 p hg
    simpa only [d8099, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41211 (p : Pattern) (guard : d8105 p = 1) : d2185 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41210 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41037 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41212 (p : Pattern) (guard : d8111 p = 1) : d2201 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41211 p hg
    simpa only [d8111, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41039 p hg
    simpa only [d8111, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41213 (p : Pattern) (guard : d8117 p = 1) : d2263 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2263, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41212 p hg
    simpa only [d8117, d2263, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2263, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41052 p hg
    simpa only [d8117, d2263, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41214 (p : Pattern) (guard : d8123 p = 1) : d2264 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2264, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41213 p hg
    simpa only [d8123, d2264, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2264, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41197 p hg
    simpa only [d8123, d2264, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41215 (p : Pattern) (guard : d8129 p = 1) : d2265 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2265, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41214 p hg
    simpa only [d8129, d2265, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2265, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41199 p hg
    simpa only [d8129, d2265, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41216 (p : Pattern) (guard : d8135 p = 1) : d2269 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2269, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41215 p hg
    simpa only [d8135, d2269, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2269, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41201 p hg
    simpa only [d8135, d2269, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41217 (p : Pattern) (guard : d8136 p = 1) : d2270 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2270, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41209 p hg
    simpa only [d8136, d2270, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2270, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41216 p hg
    simpa only [d8136, d2270, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41218 (p : Pattern) (guard : d8142 p = 1) : d2294 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d2294, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41217 p hg
    simpa only [d8142, d2294, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d2294, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d2294, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41219 (p : Pattern) (guard : d8143 p = 1) : d2295 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d2295, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41204 p hg
    simpa only [d8143, d2295, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d2295, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41218 p hg
    simpa only [d8143, d2295, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41220 (p : Pattern) (guard : d8144 p = 1) : d2296 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d2296, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41143 p hg
    simpa only [d8144, d2296, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d2296, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d8144, d2296, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41221 (p : Pattern) (guard : d8089 p = 1) : d320 p ≤ (0 : Int) + d320 p := by
  omega
theorem compare41222 (p : Pattern) (guard : d8090 p = 1) : d2318 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2318, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35696 p hg
    simpa only [d8090, d2318, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2318, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d8090, d2318, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41223 (p : Pattern) (guard : d8095 p = 1) : d2320 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2320, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d8095, d2320, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2320, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40716 p hg
    simpa only [d8095, d2320, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41224 (p : Pattern) (guard : d8100 p = 1) : d2321 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2321, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40754 p hg
    simpa only [d8100, d2321, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2321, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2321, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41225 (p : Pattern) (guard : d8101 p = 1) : d2322 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2322, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41223 p hg
    simpa only [d8101, d2322, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2322, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41224 p hg
    simpa only [d8101, d2322, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41226 (p : Pattern) (guard : d5854 p = 1) : d332 p ≤ (0 : Int) + d332 p := by
  omega
theorem compare41227 (p : Pattern) (guard : d8094 p = 1) : d2323 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2323, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35702 p hg
    simpa only [d8094, d2323, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2323, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d8094, d2323, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41228 (p : Pattern) (guard : d8100 p = 1) : d2324 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2324, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41227 p hg
    simpa only [d8100, d2324, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2324, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40671 p hg
    simpa only [d8100, d2324, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41229 (p : Pattern) (guard : d8105 p = 1) : d2321 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2321, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40863 p hg
    simpa only [d8105, d2321, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2321, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2321, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41230 (p : Pattern) (guard : d8106 p = 1) : d2325 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2325, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d8106, d2325, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2325, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41229 p hg
    simpa only [d8106, d2325, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41231 (p : Pattern) (guard : d8107 p = 1) : d2326 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2326, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41225 p hg
    simpa only [d8107, d2326, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2326, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41230 p hg
    simpa only [d8107, d2326, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41232 (p : Pattern) (guard : d8094 p = 1) : d2319 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2319, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35709 p hg
    simpa only [d8094, d2319, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2319, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2319, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41233 (p : Pattern) (guard : d8100 p = 1) : d2319 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41232 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40671 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41234 (p : Pattern) (guard : d8106 p = 1) : d2327 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2327, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41233 p hg
    simpa only [d8106, d2327, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2327, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40731 p hg
    simpa only [d8106, d2327, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41235 (p : Pattern) (guard : d8099 p = 1) : d2328 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2328, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35715 p hg
    simpa only [d8099, d2328, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2328, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2328, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41236 (p : Pattern) (guard : d8105 p = 1) : d2328 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41235 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40679 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41237 (p : Pattern) (guard : d8111 p = 1) : d2330 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2330, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41236 p hg
    simpa only [d8111, d2330, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2330, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40735 p hg
    simpa only [d8111, d2330, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41238 (p : Pattern) (guard : d8112 p = 1) : d2331 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2331, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41234 p hg
    simpa only [d8112, d2331, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2331, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41237 p hg
    simpa only [d8112, d2331, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41239 (p : Pattern) (guard : d8113 p = 1) : d2332 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2332, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41231 p hg
    simpa only [d8113, d2332, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2332, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41238 p hg
    simpa only [d8113, d2332, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41240 (p : Pattern) (guard : d8099 p = 1) : d2328 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2328, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35723 p hg
    simpa only [d8099, d2328, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2328, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2328, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41241 (p : Pattern) (guard : d8105 p = 1) : d2328 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41240 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40679 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41242 (p : Pattern) (guard : d8111 p = 1) : d2330 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2330, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41241 p hg
    simpa only [d8111, d2330, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2330, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40735 p hg
    simpa only [d8111, d2330, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41243 (p : Pattern) (guard : d8112 p = 1) : d2331 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2331, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40827 p hg
    simpa only [d8112, d2331, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2331, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41242 p hg
    simpa only [d8112, d2331, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41244 (p : Pattern) (guard : d8117 p = 1) : d2333 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2333, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40707 p hg
    simpa only [d8117, d2333, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2333, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2333, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41245 (p : Pattern) (guard : d8118 p = 1) : d2334 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2334, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41243 p hg
    simpa only [d8118, d2334, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2334, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41244 p hg
    simpa only [d8118, d2334, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41246 (p : Pattern) (guard : d8119 p = 1) : d2335 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2335, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41239 p hg
    simpa only [d8119, d2335, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2335, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41245 p hg
    simpa only [d8119, d2335, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41247 (p : Pattern) (guard : d8106 p = 1) : d2338 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2338, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40787 p hg
    simpa only [d8106, d2338, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2338, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40699 p hg
    simpa only [d8106, d2338, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41248 (p : Pattern) (guard : d8111 p = 1) : d2341 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2341, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40881 p hg
    simpa only [d8111, d2341, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2341, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40748 p hg
    simpa only [d8111, d2341, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41249 (p : Pattern) (guard : d8112 p = 1) : d2342 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2342, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41247 p hg
    simpa only [d8112, d2342, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2342, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41248 p hg
    simpa only [d8112, d2342, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41250 (p : Pattern) (guard : d8111 p = 1) : d2343 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2343, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40864 p hg
    simpa only [d8111, d2343, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2343, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2343, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41251 (p : Pattern) (guard : d8117 p = 1) : d2345 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2345, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41250 p hg
    simpa only [d8117, d2345, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2345, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40818 p hg
    simpa only [d8117, d2345, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41252 (p : Pattern) (guard : d8118 p = 1) : d2346 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2346, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41249 p hg
    simpa only [d8118, d2346, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2346, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41251 p hg
    simpa only [d8118, d2346, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41253 (p : Pattern) (guard : d8124 p = 1) : d2349 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2349, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41252 p hg
    simpa only [d8124, d2349, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2349, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40822 p hg
    simpa only [d8124, d2349, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41254 (p : Pattern) (guard : d8125 p = 1) : d2350 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2350, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41246 p hg
    simpa only [d8125, d2350, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2350, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41253 p hg
    simpa only [d8125, d2350, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41255 (p : Pattern) (guard : d5854 p = 1) : d330 p ≤ (0 : Int) + d330 p := by
  omega
theorem compare41256 (p : Pattern) (guard : d8094 p = 1) : d2351 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2351, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35746 p hg
    simpa only [d8094, d2351, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2351, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41255 p hg
    simpa only [d8094, d2351, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41257 (p : Pattern) (guard : d8100 p = 1) : d2352 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2352, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41256 p hg
    simpa only [d8100, d2352, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2352, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40863 p hg
    simpa only [d8100, d2352, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41258 (p : Pattern) (guard : d8105 p = 1) : d2321 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2321, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40880 p hg
    simpa only [d8105, d2321, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2321, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2321, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41259 (p : Pattern) (guard : d8106 p = 1) : d2353 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2353, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41257 p hg
    simpa only [d8106, d2353, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2353, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41258 p hg
    simpa only [d8106, d2353, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41260 (p : Pattern) (guard : d8099 p = 1) : d2336 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2336, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35753 p hg
    simpa only [d8099, d2336, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2336, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2336, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41261 (p : Pattern) (guard : d8105 p = 1) : d2336 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41260 p hg
    simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40719 p hg
    simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41262 (p : Pattern) (guard : d8111 p = 1) : d2354 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2354, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41261 p hg
    simpa only [d8111, d2354, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2354, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40759 p hg
    simpa only [d8111, d2354, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41263 (p : Pattern) (guard : d8112 p = 1) : d2355 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2355, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41259 p hg
    simpa only [d8112, d2355, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2355, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41262 p hg
    simpa only [d8112, d2355, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41264 (p : Pattern) (guard : d8099 p = 1) : d2328 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2328, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35760 p hg
    simpa only [d8099, d2328, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2328, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2328, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41265 (p : Pattern) (guard : d8105 p = 1) : d2328 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41264 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40679 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41266 (p : Pattern) (guard : d8111 p = 1) : d2330 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2330, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41265 p hg
    simpa only [d8111, d2330, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2330, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40735 p hg
    simpa only [d8111, d2330, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41267 (p : Pattern) (guard : d8117 p = 1) : d2444 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2444, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41266 p hg
    simpa only [d8117, d2444, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2444, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35764 p hg
    simpa only [d8117, d2444, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41268 (p : Pattern) (guard : d8118 p = 1) : d2445 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2445, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41263 p hg
    simpa only [d8118, d2445, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2445, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41267 p hg
    simpa only [d8118, d2445, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41269 (p : Pattern) (guard : d8117 p = 1) : d2444 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2444, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41237 p hg
    simpa only [d8117, d2444, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2444, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35767 p hg
    simpa only [d8117, d2444, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41270 (p : Pattern) (guard : d8123 p = 1) : d2446 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2446, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41269 p hg
    simpa only [d8123, d2446, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2446, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2446, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41271 (p : Pattern) (guard : d8124 p = 1) : d2447 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2447, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41268 p hg
    simpa only [d8124, d2447, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2447, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41270 p hg
    simpa only [d8124, d2447, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41272 (p : Pattern) (guard : d8099 p = 1) : d2319 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2319, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35773 p hg
    simpa only [d8099, d2319, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2319, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2319, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41273 (p : Pattern) (guard : d8105 p = 1) : d2319 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41272 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40813 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41274 (p : Pattern) (guard : d8111 p = 1) : d2341 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2341, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41273 p hg
    simpa only [d8111, d2341, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2341, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40748 p hg
    simpa only [d8111, d2341, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41275 (p : Pattern) (guard : d8117 p = 1) : d2362 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2362, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41274 p hg
    simpa only [d8117, d2362, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2362, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40840 p hg
    simpa only [d8117, d2362, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41276 (p : Pattern) (guard : d0 p = 1) : d2448 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41277 (p : Pattern) (guard : d8123 p = 1) : d2449 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2449, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41275 p hg
    simpa only [d8123, d2449, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2449, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41276 p hg
    simpa only [d8123, d2449, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41278 (p : Pattern) (guard : d0 p = 1) : d2450 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41279 (p : Pattern) (guard : d8129 p = 1) : d2451 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2451, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41277 p hg
    simpa only [d8129, d2451, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2451, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41278 p hg
    simpa only [d8129, d2451, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41280 (p : Pattern) (guard : d8130 p = 1) : d2452 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2452, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41271 p hg
    simpa only [d8130, d2452, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2452, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41279 p hg
    simpa only [d8130, d2452, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41281 (p : Pattern) (guard : d8131 p = 1) : d2453 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2453, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41254 p hg
    simpa only [d8131, d2453, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2453, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41280 p hg
    simpa only [d8131, d2453, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41282 (p : Pattern) (guard : d8111 p = 1) : d2327 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2327, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41273 p hg
    simpa only [d8111, d2327, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2327, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d8111, d2327, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41283 (p : Pattern) (guard : d8112 p = 1) : d2327 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40827 p hg
    simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41282 p hg
    simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41284 (p : Pattern) (guard : d8117 p = 1) : d2331 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2331, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40882 p hg
    simpa only [d8117, d2331, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2331, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40851 p hg
    simpa only [d8117, d2331, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41285 (p : Pattern) (guard : d8118 p = 1) : d2370 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2370, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41283 p hg
    simpa only [d8118, d2370, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2370, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41284 p hg
    simpa only [d8118, d2370, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41286 (p : Pattern) (guard : d8117 p = 1) : d2331 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2331, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40865 p hg
    simpa only [d8117, d2331, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2331, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40851 p hg
    simpa only [d8117, d2331, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41287 (p : Pattern) (guard : d8123 p = 1) : d2334 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2334, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41286 p hg
    simpa only [d8123, d2334, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2334, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40854 p hg
    simpa only [d8123, d2334, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41288 (p : Pattern) (guard : d8124 p = 1) : d2371 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2371, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41285 p hg
    simpa only [d8124, d2371, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2371, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41287 p hg
    simpa only [d8124, d2371, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41289 (p : Pattern) (guard : d8130 p = 1) : d2376 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2376, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41288 p hg
    simpa only [d8130, d2376, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2376, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40861 p hg
    simpa only [d8130, d2376, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41290 (p : Pattern) (guard : d8099 p = 1) : d2319 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2319, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35794 p hg
    simpa only [d8099, d2319, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2319, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2319, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41291 (p : Pattern) (guard : d8105 p = 1) : d2319 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41290 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40813 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41292 (p : Pattern) (guard : d8111 p = 1) : d2327 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2327, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41291 p hg
    simpa only [d8111, d2327, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2327, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d8111, d2327, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41293 (p : Pattern) (guard : d0 p = 1) : d2354 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41294 (p : Pattern) (guard : d8117 p = 1) : d2377 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2377, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41292 p hg
    simpa only [d8117, d2377, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2377, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41293 p hg
    simpa only [d8117, d2377, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41295 (p : Pattern) (guard : d0 p = 1) : d2444 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41296 (p : Pattern) (guard : d8123 p = 1) : d2454 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2454, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41294 p hg
    simpa only [d8123, d2454, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2454, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41295 p hg
    simpa only [d8123, d2454, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41297 (p : Pattern) (guard : d0 p = 1) : d2446 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41298 (p : Pattern) (guard : d8129 p = 1) : d2455 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2455, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41296 p hg
    simpa only [d8129, d2455, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2455, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41297 p hg
    simpa only [d8129, d2455, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41299 (p : Pattern) (guard : d8135 p = 1) : d2456 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2456, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41298 p hg
    simpa only [d8135, d2456, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2456, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40872 p hg
    simpa only [d8135, d2456, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
