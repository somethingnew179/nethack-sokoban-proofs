/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons265
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare37240 (p : Pattern) (guard : d8112 p = 1) : d3840 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3840, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37239 p hg
    simpa only [d8112, d3840, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3840, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37196 p hg
    simpa only [d8112, d3840, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37241 (p : Pattern) (guard : d8118 p = 1) : d3841 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3841, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37240 p hg
    simpa only [d8118, d3841, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3841, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3841, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37242 (p : Pattern) (guard : d8124 p = 1) : d3842 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3842, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37241 p hg
    simpa only [d8124, d3842, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3842, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3842, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37243 (p : Pattern) (guard : d8125 p = 1) : d3843 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3843, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37233 p hg
    simpa only [d8125, d3843, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3843, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37242 p hg
    simpa only [d8125, d3843, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37244 (p : Pattern) (guard : d8084 p = 1) : d102 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1404 p hg
    simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37245 (p : Pattern) (guard : d8089 p = 1) : d102 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37244 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37003 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37246 (p : Pattern) (guard : d8094 p = 1) : d102 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37245 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37073 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37247 (p : Pattern) (guard : d8100 p = 1) : d3766 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3766, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37246 p hg
    simpa only [d8100, d3766, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3766, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37076 p hg
    simpa only [d8100, d3766, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37248 (p : Pattern) (guard : d8106 p = 1) : d3827 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3827, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37247 p hg
    simpa only [d8106, d3827, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3827, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37170 p hg
    simpa only [d8106, d3827, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37249 (p : Pattern) (guard : d5843 p = 1) : d115 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d115, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10938 p hg
    simpa only [d5843, d115, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d115, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d115, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37250 (p : Pattern) (guard : d5847 p = 1) : d115 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37249 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37251 (p : Pattern) (guard : d5854 p = 1) : d115 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37250 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37252 (p : Pattern) (guard : d8099 p = 1) : d115 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37251 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37253 (p : Pattern) (guard : d8105 p = 1) : d3808 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3808, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37252 p hg
    simpa only [d8105, d3808, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3808, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37152 p hg
    simpa only [d8105, d3808, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37254 (p : Pattern) (guard : d8111 p = 1) : d3837 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3837, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37253 p hg
    simpa only [d8111, d3837, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3837, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37211 p hg
    simpa only [d8111, d3837, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37255 (p : Pattern) (guard : d8112 p = 1) : d3844 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3844, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37248 p hg
    simpa only [d8112, d3844, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3844, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37254 p hg
    simpa only [d8112, d3844, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37256 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1265 p hg
    simpa only [d5843, d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37257 (p : Pattern) (guard : d5847 p = 1) : d106 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37256 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37258 (p : Pattern) (guard : d5854 p = 1) : d106 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37257 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37259 (p : Pattern) (guard : d8099 p = 1) : d106 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37258 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37260 (p : Pattern) (guard : d8105 p = 1) : d3786 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3786, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37259 p hg
    simpa only [d8105, d3786, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3786, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37089 p hg
    simpa only [d8105, d3786, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37261 (p : Pattern) (guard : d8111 p = 1) : d3832 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3832, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37260 p hg
    simpa only [d8111, d3832, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3832, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37175 p hg
    simpa only [d8111, d3832, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37262 (p : Pattern) (guard : d8117 p = 1) : d3845 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3845, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37261 p hg
    simpa only [d8117, d3845, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3845, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36782 p hg
    simpa only [d8117, d3845, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37263 (p : Pattern) (guard : d8118 p = 1) : d3846 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3846, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37255 p hg
    simpa only [d8118, d3846, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3846, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37262 p hg
    simpa only [d8118, d3846, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37264 (p : Pattern) (guard : d8124 p = 1) : d3849 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3849, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37263 p hg
    simpa only [d8124, d3849, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3849, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37218 p hg
    simpa only [d8124, d3849, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37265 (p : Pattern) (guard : d8130 p = 1) : d3853 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3853, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37264 p hg
    simpa only [d8130, d3853, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3853, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37222 p hg
    simpa only [d8130, d3853, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37266 (p : Pattern) (guard : d8131 p = 1) : d3854 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3854, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37243 p hg
    simpa only [d8131, d3854, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3854, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37265 p hg
    simpa only [d8131, d3854, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37267 (p : Pattern) (guard : d8118 p = 1) : d3856 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3856, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37052 p hg
    simpa only [d8118, d3856, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3856, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3856, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37268 (p : Pattern) (guard : d8124 p = 1) : d3857 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3857, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37267 p hg
    simpa only [d8124, d3857, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3857, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3857, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37269 (p : Pattern) (guard : d8130 p = 1) : d3858 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3858, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37268 p hg
    simpa only [d8130, d3858, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3858, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d3858, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37270 (p : Pattern) (guard : d8135 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare37271 (p : Pattern) (guard : d8136 p = 1) : d3859 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3859, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37269 p hg
    simpa only [d8136, d3859, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3859, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37270 p hg
    simpa only [d8136, d3859, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37272 (p : Pattern) (guard : d8137 p = 1) : d3860 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3860, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37266 p hg
    simpa only [d8137, d3860, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3860, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37271 p hg
    simpa only [d8137, d3860, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37273 (p : Pattern) (guard : d8138 p = 1) : d3861 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d3861, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37225 p hg
    simpa only [d8138, d3861, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d3861, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37272 p hg
    simpa only [d8138, d3861, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37274 (p : Pattern) (guard : d5854 p = 1) : d3737 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37003 p hg
    simpa only [d5854, d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29469 p hg
    simpa only [d5854, d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37275 (p : Pattern) (guard : d8099 p = 1) : d3738 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37274 p hg
    simpa only [d8099, d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29469 p hg
    simpa only [d8099, d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37276 (p : Pattern) (guard : d8100 p = 1) : d3745 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3745, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37246 p hg
    simpa only [d8100, d3745, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3745, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37275 p hg
    simpa only [d8100, d3745, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37277 (p : Pattern) (guard : d5854 p = 1) : d3741 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37003 p hg
    simpa only [d5854, d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29476 p hg
    simpa only [d5854, d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37278 (p : Pattern) (guard : d8099 p = 1) : d3742 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37277 p hg
    simpa only [d8099, d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29476 p hg
    simpa only [d8099, d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37279 (p : Pattern) (guard : d8105 p = 1) : d3743 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37278 p hg
    simpa only [d8105, d3743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37280 (p : Pattern) (guard : d8106 p = 1) : d3746 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3746, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37276 p hg
    simpa only [d8106, d3746, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3746, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37279 p hg
    simpa only [d8106, d3746, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37281 (p : Pattern) (guard : d8107 p = 1) : d3746 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37014 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37280 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37282 (p : Pattern) (guard : d8100 p = 1) : d3745 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3745, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37203 p hg
    simpa only [d8100, d3745, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3745, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37275 p hg
    simpa only [d8100, d3745, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37283 (p : Pattern) (guard : d8106 p = 1) : d3746 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3746, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37282 p hg
    simpa only [d8106, d3746, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3746, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37279 p hg
    simpa only [d8106, d3746, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37284 (p : Pattern) (guard : d0 p = 1) : d3750 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37285 (p : Pattern) (guard : d8105 p = 1) : d3751 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3751, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37259 p hg
    simpa only [d8105, d3751, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3751, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37284 p hg
    simpa only [d8105, d3751, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37286 (p : Pattern) (guard : d0 p = 1) : d3755 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37287 (p : Pattern) (guard : d8111 p = 1) : d3756 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3756, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37285 p hg
    simpa only [d8111, d3756, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3756, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37286 p hg
    simpa only [d8111, d3756, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37288 (p : Pattern) (guard : d8112 p = 1) : d3757 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3757, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37283 p hg
    simpa only [d8112, d3757, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3757, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37287 p hg
    simpa only [d8112, d3757, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37289 (p : Pattern) (guard : d8113 p = 1) : d3862 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3862, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37281 p hg
    simpa only [d8113, d3862, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3862, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37288 p hg
    simpa only [d8113, d3862, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37290 (p : Pattern) (guard : d8100 p = 1) : d3745 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3745, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37148 p hg
    simpa only [d8100, d3745, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3745, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37275 p hg
    simpa only [d8100, d3745, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37291 (p : Pattern) (guard : d8106 p = 1) : d3746 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3746, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37290 p hg
    simpa only [d8106, d3746, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3746, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37279 p hg
    simpa only [d8106, d3746, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37292 (p : Pattern) (guard : d8105 p = 1) : d3751 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37088 p hg
    simpa only [d8105, d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37284 p hg
    simpa only [d8105, d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37293 (p : Pattern) (guard : d8111 p = 1) : d3756 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37292 p hg
    simpa only [d8111, d3756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37286 p hg
    simpa only [d8111, d3756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37294 (p : Pattern) (guard : d8112 p = 1) : d3757 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3757, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37291 p hg
    simpa only [d8112, d3757, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3757, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37293 p hg
    simpa only [d8112, d3757, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37295 (p : Pattern) (guard : d8118 p = 1) : d3760 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3760, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37294 p hg
    simpa only [d8118, d3760, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3760, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37181 p hg
    simpa only [d8118, d3760, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37296 (p : Pattern) (guard : d8119 p = 1) : d3863 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3863, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37289 p hg
    simpa only [d8119, d3863, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3863, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37295 p hg
    simpa only [d8119, d3863, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37297 (p : Pattern) (guard : d8106 p = 1) : d3773 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3773, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37077 p hg
    simpa only [d8106, d3773, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3773, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37189 p hg
    simpa only [d8106, d3773, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37298 (p : Pattern) (guard : d8099 p = 1) : d102 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37073 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37299 (p : Pattern) (guard : d0 p = 1) : d3765 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37300 (p : Pattern) (guard : d8105 p = 1) : d3766 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37298 p hg
    simpa only [d8105, d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37299 p hg
    simpa only [d8105, d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37301 (p : Pattern) (guard : d8111 p = 1) : d3779 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37300 p hg
    simpa only [d8111, d3779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37195 p hg
    simpa only [d8111, d3779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37302 (p : Pattern) (guard : d8112 p = 1) : d3780 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3780, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37297 p hg
    simpa only [d8112, d3780, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3780, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37301 p hg
    simpa only [d8112, d3780, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37303 (p : Pattern) (guard : d8111 p = 1) : d3781 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37300 p hg
    simpa only [d8111, d3781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37304 (p : Pattern) (guard : d0 p = 1) : d3787 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37305 (p : Pattern) (guard : d8117 p = 1) : d3788 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37303 p hg
    simpa only [d8117, d3788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37304 p hg
    simpa only [d8117, d3788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37306 (p : Pattern) (guard : d8118 p = 1) : d3789 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3789, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37302 p hg
    simpa only [d8118, d3789, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3789, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37305 p hg
    simpa only [d8118, d3789, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37307 (p : Pattern) (guard : d0 p = 1) : d3790 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37308 (p : Pattern) (guard : d8123 p = 1) : d3791 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37305 p hg
    simpa only [d8123, d3791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37307 p hg
    simpa only [d8123, d3791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37309 (p : Pattern) (guard : d8124 p = 1) : d3792 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3792, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37306 p hg
    simpa only [d8124, d3792, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3792, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37308 p hg
    simpa only [d8124, d3792, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37310 (p : Pattern) (guard : d8125 p = 1) : d3864 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3864, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37296 p hg
    simpa only [d8125, d3864, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3864, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37309 p hg
    simpa only [d8125, d3864, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37311 (p : Pattern) (guard : d8084 p = 1) : d102 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37040 p hg
    simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37312 (p : Pattern) (guard : d8089 p = 1) : d102 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37311 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37003 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37313 (p : Pattern) (guard : d8094 p = 1) : d102 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37312 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37073 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37314 (p : Pattern) (guard : d8100 p = 1) : d3745 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3745, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37313 p hg
    simpa only [d8100, d3745, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3745, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37275 p hg
    simpa only [d8100, d3745, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37315 (p : Pattern) (guard : d8106 p = 1) : d3746 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3746, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37314 p hg
    simpa only [d8106, d3746, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3746, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37279 p hg
    simpa only [d8106, d3746, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37316 (p : Pattern) (guard : d5843 p = 1) : d115 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d115, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4566 p hg
    simpa only [d5843, d115, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d115, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d115, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37317 (p : Pattern) (guard : d5847 p = 1) : d115 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37316 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37318 (p : Pattern) (guard : d5854 p = 1) : d115 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37317 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37319 (p : Pattern) (guard : d8099 p = 1) : d115 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37318 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37320 (p : Pattern) (guard : d0 p = 1) : d3795 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37321 (p : Pattern) (guard : d8105 p = 1) : d3796 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3796, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37319 p hg
    simpa only [d8105, d3796, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3796, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37320 p hg
    simpa only [d8105, d3796, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37322 (p : Pattern) (guard : d0 p = 1) : d3800 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37323 (p : Pattern) (guard : d8111 p = 1) : d3801 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3801, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37321 p hg
    simpa only [d8111, d3801, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3801, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37322 p hg
    simpa only [d8111, d3801, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37324 (p : Pattern) (guard : d8112 p = 1) : d3802 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3802, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37315 p hg
    simpa only [d8112, d3802, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3802, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37323 p hg
    simpa only [d8112, d3802, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37325 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1258 p hg
    simpa only [d5843, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37326 (p : Pattern) (guard : d5847 p = 1) : d106 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37325 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37327 (p : Pattern) (guard : d5854 p = 1) : d106 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37326 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37328 (p : Pattern) (guard : d8099 p = 1) : d106 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37327 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37329 (p : Pattern) (guard : d8105 p = 1) : d3751 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3751, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37328 p hg
    simpa only [d8105, d3751, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3751, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37284 p hg
    simpa only [d8105, d3751, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37330 (p : Pattern) (guard : d8111 p = 1) : d3756 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3756, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37329 p hg
    simpa only [d8111, d3756, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3756, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37286 p hg
    simpa only [d8111, d3756, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37331 (p : Pattern) (guard : d8117 p = 1) : d3803 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3803, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37330 p hg
    simpa only [d8117, d3803, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3803, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36782 p hg
    simpa only [d8117, d3803, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37332 (p : Pattern) (guard : d8118 p = 1) : d3804 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3804, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37324 p hg
    simpa only [d8118, d3804, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3804, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37331 p hg
    simpa only [d8118, d3804, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37333 (p : Pattern) (guard : d8117 p = 1) : d3805 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3805, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37287 p hg
    simpa only [d8117, d3805, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3805, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37216 p hg
    simpa only [d8117, d3805, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37334 (p : Pattern) (guard : d8123 p = 1) : d3806 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3806, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37333 p hg
    simpa only [d8123, d3806, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3806, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3806, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37335 (p : Pattern) (guard : d8124 p = 1) : d3807 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3807, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37332 p hg
    simpa only [d8124, d3807, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3807, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37334 p hg
    simpa only [d8124, d3807, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37336 (p : Pattern) (guard : d0 p = 1) : d3809 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37337 (p : Pattern) (guard : d8117 p = 1) : d3810 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37301 p hg
    simpa only [d8117, d3810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37336 p hg
    simpa only [d8117, d3810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37338 (p : Pattern) (guard : d0 p = 1) : d3811 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37339 (p : Pattern) (guard : d8123 p = 1) : d3812 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37337 p hg
    simpa only [d8123, d3812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37338 p hg
    simpa only [d8123, d3812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37340 (p : Pattern) (guard : d0 p = 1) : d3814 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37341 (p : Pattern) (guard : d8129 p = 1) : d3815 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37339 p hg
    simpa only [d8129, d3815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37340 p hg
    simpa only [d8129, d3815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37342 (p : Pattern) (guard : d8130 p = 1) : d3816 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3816, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37335 p hg
    simpa only [d8130, d3816, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3816, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37341 p hg
    simpa only [d8130, d3816, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37343 (p : Pattern) (guard : d8131 p = 1) : d3865 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3865, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37310 p hg
    simpa only [d8131, d3865, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3865, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37342 p hg
    simpa only [d8131, d3865, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37344 (p : Pattern) (guard : d8099 p = 1) : d3819 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37075 p hg
    simpa only [d8099, d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31856 p hg
    simpa only [d8099, d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37345 (p : Pattern) (guard : d8100 p = 1) : d3820 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3820, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37148 p hg
    simpa only [d8100, d3820, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3820, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37344 p hg
    simpa only [d8100, d3820, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37346 (p : Pattern) (guard : d8105 p = 1) : d3821 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37275 p hg
    simpa only [d8105, d3821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37347 (p : Pattern) (guard : d8106 p = 1) : d3822 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3822, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37345 p hg
    simpa only [d8106, d3822, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3822, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37346 p hg
    simpa only [d8106, d3822, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37348 (p : Pattern) (guard : d0 p = 1) : d3826 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37349 (p : Pattern) (guard : d8111 p = 1) : d3827 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37300 p hg
    simpa only [d8111, d3827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37348 p hg
    simpa only [d8111, d3827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37350 (p : Pattern) (guard : d8112 p = 1) : d3828 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3828, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37347 p hg
    simpa only [d8112, d3828, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3828, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37349 p hg
    simpa only [d8112, d3828, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37351 (p : Pattern) (guard : d0 p = 1) : d3829 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37352 (p : Pattern) (guard : d8111 p = 1) : d3830 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37300 p hg
    simpa only [d8111, d3830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37351 p hg
    simpa only [d8111, d3830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37353 (p : Pattern) (guard : d0 p = 1) : d3832 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37354 (p : Pattern) (guard : d8117 p = 1) : d3833 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37352 p hg
    simpa only [d8117, d3833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37353 p hg
    simpa only [d8117, d3833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37355 (p : Pattern) (guard : d8118 p = 1) : d3834 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3834, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37350 p hg
    simpa only [d8118, d3834, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3834, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37354 p hg
    simpa only [d8118, d3834, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37356 (p : Pattern) (guard : d0 p = 1) : d3759 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37357 (p : Pattern) (guard : d8123 p = 1) : d3835 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37354 p hg
    simpa only [d8123, d3835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37356 p hg
    simpa only [d8123, d3835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37358 (p : Pattern) (guard : d8124 p = 1) : d3836 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3836, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37355 p hg
    simpa only [d8124, d3836, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3836, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37357 p hg
    simpa only [d8124, d3836, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37359 (p : Pattern) (guard : d8111 p = 1) : d3837 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37153 p hg
    simpa only [d8111, d3837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37211 p hg
    simpa only [d8111, d3837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37360 (p : Pattern) (guard : d0 p = 1) : d3839 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37361 (p : Pattern) (guard : d8117 p = 1) : d3840 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37359 p hg
    simpa only [d8117, d3840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37360 p hg
    simpa only [d8117, d3840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37362 (p : Pattern) (guard : d8123 p = 1) : d3841 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37361 p hg
    simpa only [d8123, d3841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37363 (p : Pattern) (guard : d8129 p = 1) : d3842 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37362 p hg
    simpa only [d8129, d3842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37364 (p : Pattern) (guard : d8130 p = 1) : d3843 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3843, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37358 p hg
    simpa only [d8130, d3843, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3843, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37363 p hg
    simpa only [d8130, d3843, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37365 (p : Pattern) (guard : d5847 p = 1) : d102 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35744 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37366 (p : Pattern) (guard : d5854 p = 1) : d102 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37365 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37367 (p : Pattern) (guard : d8099 p = 1) : d102 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37366 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37368 (p : Pattern) (guard : d8105 p = 1) : d3766 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3766, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37367 p hg
    simpa only [d8105, d3766, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3766, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37299 p hg
    simpa only [d8105, d3766, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37369 (p : Pattern) (guard : d8111 p = 1) : d3827 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3827, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37368 p hg
    simpa only [d8111, d3827, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3827, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37348 p hg
    simpa only [d8111, d3827, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37370 (p : Pattern) (guard : d0 p = 1) : d3837 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37371 (p : Pattern) (guard : d8117 p = 1) : d3844 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3844, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37369 p hg
    simpa only [d8117, d3844, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3844, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37370 p hg
    simpa only [d8117, d3844, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37372 (p : Pattern) (guard : d0 p = 1) : d3845 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37373 (p : Pattern) (guard : d8123 p = 1) : d3846 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3846, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37371 p hg
    simpa only [d8123, d3846, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3846, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37372 p hg
    simpa only [d8123, d3846, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37374 (p : Pattern) (guard : d0 p = 1) : d3848 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37375 (p : Pattern) (guard : d8129 p = 1) : d3849 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3849, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37373 p hg
    simpa only [d8129, d3849, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3849, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37374 p hg
    simpa only [d8129, d3849, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37376 (p : Pattern) (guard : d0 p = 1) : d3852 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37377 (p : Pattern) (guard : d8135 p = 1) : d3853 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3853, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37375 p hg
    simpa only [d8135, d3853, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3853, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37376 p hg
    simpa only [d8135, d3853, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37378 (p : Pattern) (guard : d8136 p = 1) : d3854 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3854, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37364 p hg
    simpa only [d8136, d3854, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3854, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37377 p hg
    simpa only [d8136, d3854, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37379 (p : Pattern) (guard : d8137 p = 1) : d3866 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3866, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37343 p hg
    simpa only [d8137, d3866, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3866, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37378 p hg
    simpa only [d8137, d3866, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
