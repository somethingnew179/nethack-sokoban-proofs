/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons337
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare47320 (p : Pattern) (guard : d0 p = 1) : d2961 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47321 (p : Pattern) (guard : d8117 p = 1) : d3127 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3127, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47319 p hg
    simpa only [d8117, d3127, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3127, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47320 p hg
    simpa only [d8117, d3127, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47322 (p : Pattern) (guard : d0 p = 1) : d3128 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47323 (p : Pattern) (guard : d8123 p = 1) : d3129 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3129, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47321 p hg
    simpa only [d8123, d3129, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3129, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47322 p hg
    simpa only [d8123, d3129, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47324 (p : Pattern) (guard : d0 p = 1) : d2975 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47325 (p : Pattern) (guard : d8129 p = 1) : d3130 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3130, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47323 p hg
    simpa only [d8129, d3130, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3130, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47324 p hg
    simpa only [d8129, d3130, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47326 (p : Pattern) (guard : d0 p = 1) : d3133 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47327 (p : Pattern) (guard : d8135 p = 1) : d3134 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3134, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47325 p hg
    simpa only [d8135, d3134, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3134, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47326 p hg
    simpa only [d8135, d3134, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47328 (p : Pattern) (guard : d8136 p = 1) : d3135 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3135, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47318 p hg
    simpa only [d8136, d3135, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3135, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47327 p hg
    simpa only [d8136, d3135, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47329 (p : Pattern) (guard : d8137 p = 1) : d3136 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3136, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47303 p hg
    simpa only [d8137, d3136, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3136, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47328 p hg
    simpa only [d8137, d3136, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47330 (p : Pattern) (guard : d8100 p = 1) : d3114 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3114, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35464 p hg
    simpa only [d8100, d3114, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3114, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38950 p hg
    simpa only [d8100, d3114, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47331 (p : Pattern) (guard : d8106 p = 1) : d3115 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3115, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47330 p hg
    simpa only [d8106, d3115, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3115, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39563 p hg
    simpa only [d8106, d3115, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47332 (p : Pattern) (guard : d8105 p = 1) : d2906 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35551 p hg
    simpa only [d8105, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23891 p hg
    simpa only [d8105, d2906, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47333 (p : Pattern) (guard : d8111 p = 1) : d3116 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3116, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47332 p hg
    simpa only [d8111, d3116, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3116, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15552 p hg
    simpa only [d8111, d3116, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47334 (p : Pattern) (guard : d8112 p = 1) : d3117 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3117, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47331 p hg
    simpa only [d8112, d3117, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3117, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47333 p hg
    simpa only [d8112, d3117, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47335 (p : Pattern) (guard : d8118 p = 1) : d3118 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3118, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47334 p hg
    simpa only [d8118, d3118, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3118, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47310 p hg
    simpa only [d8118, d3118, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47336 (p : Pattern) (guard : d8124 p = 1) : d3119 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3119, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47335 p hg
    simpa only [d8124, d3119, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3119, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47312 p hg
    simpa only [d8124, d3119, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47337 (p : Pattern) (guard : d8130 p = 1) : d3125 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3125, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47336 p hg
    simpa only [d8130, d3125, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3125, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47317 p hg
    simpa only [d8130, d3125, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47338 (p : Pattern) (guard : d8111 p = 1) : d3126 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3126, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47235 p hg
    simpa only [d8111, d3126, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3126, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15565 p hg
    simpa only [d8111, d3126, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47339 (p : Pattern) (guard : d8117 p = 1) : d3127 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3127, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47338 p hg
    simpa only [d8117, d3127, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3127, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47320 p hg
    simpa only [d8117, d3127, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47340 (p : Pattern) (guard : d8123 p = 1) : d3129 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3129, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47339 p hg
    simpa only [d8123, d3129, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3129, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47322 p hg
    simpa only [d8123, d3129, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47341 (p : Pattern) (guard : d8129 p = 1) : d3130 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3130, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47340 p hg
    simpa only [d8129, d3130, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3130, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47324 p hg
    simpa only [d8129, d3130, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47342 (p : Pattern) (guard : d8135 p = 1) : d3134 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3134, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47341 p hg
    simpa only [d8135, d3134, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3134, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47326 p hg
    simpa only [d8135, d3134, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47343 (p : Pattern) (guard : d8136 p = 1) : d3135 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3135, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47337 p hg
    simpa only [d8136, d3135, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3135, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47342 p hg
    simpa only [d8136, d3135, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47344 (p : Pattern) (guard : d8142 p = 1) : d3137 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d3137, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47343 p hg
    simpa only [d8142, d3137, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d3137, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d3137, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47345 (p : Pattern) (guard : d8143 p = 1) : d3138 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d3138, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47329 p hg
    simpa only [d8143, d3138, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d3138, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47344 p hg
    simpa only [d8143, d3138, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47346 (p : Pattern) (guard : d8144 p = 1) : d3139 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d3139, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47255 p hg
    simpa only [d8144, d3139, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d3139, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47345 p hg
    simpa only [d8144, d3139, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47347 (p : Pattern) (guard : d8145 p = 1) : d3140 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d3140, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46900 p hg
    simpa only [d8145, d3140, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d3140, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47346 p hg
    simpa only [d8145, d3140, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47348 (p : Pattern) (guard : d8085 p = 1) : d1771 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1771, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34319 p hg
    simpa only [d8085, d1771, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1771, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38480 p hg
    simpa only [d8085, d1771, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47349 (p : Pattern) (guard : d8090 p = 1) : d1772 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1772, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47348 p hg
    simpa only [d8090, d1772, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1772, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38702 p hg
    simpa only [d8090, d1772, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47350 (p : Pattern) (guard : d8091 p = 1) : d2895 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2895, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35563 p hg
    simpa only [d8091, d2895, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2895, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47349 p hg
    simpa only [d8091, d2895, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47351 (p : Pattern) (guard : d8096 p = 1) : d2896 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2896, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47350 p hg
    simpa only [d8096, d2896, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2896, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39609 p hg
    simpa only [d8096, d2896, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47352 (p : Pattern) (guard : d8102 p = 1) : d2896 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47351 p hg
    simpa only [d8102, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47180 p hg
    simpa only [d8102, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47353 (p : Pattern) (guard : d8107 p = 1) : d2899 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2899, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47159 p hg
    simpa only [d8107, d2899, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2899, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47185 p hg
    simpa only [d8107, d2899, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47354 (p : Pattern) (guard : d8108 p = 1) : d2900 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2900, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47352 p hg
    simpa only [d8108, d2900, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2900, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47353 p hg
    simpa only [d8108, d2900, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47355 (p : Pattern) (guard : d8112 p = 1) : d2903 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2903, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46796 p hg
    simpa only [d8112, d2903, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2903, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2903, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47356 (p : Pattern) (guard : d8113 p = 1) : d2904 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2904, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47163 p hg
    simpa only [d8113, d2904, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2904, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47355 p hg
    simpa only [d8113, d2904, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47357 (p : Pattern) (guard : d8114 p = 1) : d2905 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2905, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47354 p hg
    simpa only [d8114, d2905, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2905, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47356 p hg
    simpa only [d8114, d2905, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47358 (p : Pattern) (guard : d8095 p = 1) : d2906 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2906, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d8095, d2906, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2906, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38715 p hg
    simpa only [d8095, d2906, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47359 (p : Pattern) (guard : d8101 p = 1) : d2907 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2907, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47358 p hg
    simpa only [d8101, d2907, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2907, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d2907, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47360 (p : Pattern) (guard : d8107 p = 1) : d2909 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2909, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47359 p hg
    simpa only [d8107, d2909, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2909, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47196 p hg
    simpa only [d8107, d2909, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47361 (p : Pattern) (guard : d8106 p = 1) : d2910 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2910, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47171 p hg
    simpa only [d8106, d2910, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2910, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38569 p hg
    simpa only [d8106, d2910, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47362 (p : Pattern) (guard : d8112 p = 1) : d2913 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2913, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47361 p hg
    simpa only [d8112, d2913, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2913, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46672 p hg
    simpa only [d8112, d2913, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47363 (p : Pattern) (guard : d8113 p = 1) : d2914 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2914, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47360 p hg
    simpa only [d8113, d2914, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2914, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47362 p hg
    simpa only [d8113, d2914, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47364 (p : Pattern) (guard : d8106 p = 1) : d2915 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2915, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46875 p hg
    simpa only [d8106, d2915, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2915, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2915, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47365 (p : Pattern) (guard : d8112 p = 1) : d2916 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2916, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47364 p hg
    simpa only [d8112, d2916, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2916, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46672 p hg
    simpa only [d8112, d2916, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47366 (p : Pattern) (guard : d8118 p = 1) : d2919 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2919, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47365 p hg
    simpa only [d8118, d2919, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2919, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d8118, d2919, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47367 (p : Pattern) (guard : d8119 p = 1) : d2920 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2920, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47363 p hg
    simpa only [d8119, d2920, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2920, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47366 p hg
    simpa only [d8119, d2920, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47368 (p : Pattern) (guard : d8120 p = 1) : d2921 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2921, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47357 p hg
    simpa only [d8120, d2921, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2921, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47367 p hg
    simpa only [d8120, d2921, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47369 (p : Pattern) (guard : d8089 p = 1) : d1771 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1771, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35069 p hg
    simpa only [d8089, d1771, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1771, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38701 p hg
    simpa only [d8089, d1771, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47370 (p : Pattern) (guard : d8094 p = 1) : d1772 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1772, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47369 p hg
    simpa only [d8094, d1772, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1772, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38944 p hg
    simpa only [d8094, d1772, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47371 (p : Pattern) (guard : d8095 p = 1) : d2895 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2895, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35584 p hg
    simpa only [d8095, d2895, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2895, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47370 p hg
    simpa only [d8095, d2895, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47372 (p : Pattern) (guard : d8101 p = 1) : d2896 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2896, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47371 p hg
    simpa only [d8101, d2896, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2896, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39631 p hg
    simpa only [d8101, d2896, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47373 (p : Pattern) (guard : d8100 p = 1) : d2922 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2922, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35590 p hg
    simpa only [d8100, d2922, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2922, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46684 p hg
    simpa only [d8100, d2922, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47374 (p : Pattern) (guard : d8106 p = 1) : d2923 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2923, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47373 p hg
    simpa only [d8106, d2923, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2923, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38920 p hg
    simpa only [d8106, d2923, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47375 (p : Pattern) (guard : d8107 p = 1) : d2924 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2924, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47372 p hg
    simpa only [d8107, d2924, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2924, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47374 p hg
    simpa only [d8107, d2924, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47376 (p : Pattern) (guard : d8100 p = 1) : d2897 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2897, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35596 p hg
    simpa only [d8100, d2897, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2897, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46653 p hg
    simpa only [d8100, d2897, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47377 (p : Pattern) (guard : d8106 p = 1) : d2898 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2898, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47376 p hg
    simpa only [d8106, d2898, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2898, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38892 p hg
    simpa only [d8106, d2898, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47378 (p : Pattern) (guard : d8105 p = 1) : d2901 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35600 p hg
    simpa only [d8105, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23885 p hg
    simpa only [d8105, d2901, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47379 (p : Pattern) (guard : d8111 p = 1) : d2902 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47378 p hg
    simpa only [d8111, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15276 p hg
    simpa only [d8111, d2902, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47380 (p : Pattern) (guard : d8112 p = 1) : d2925 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2925, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47377 p hg
    simpa only [d8112, d2925, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2925, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47379 p hg
    simpa only [d8112, d2925, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47381 (p : Pattern) (guard : d8113 p = 1) : d2926 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2926, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47375 p hg
    simpa only [d8113, d2926, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2926, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47380 p hg
    simpa only [d8113, d2926, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47382 (p : Pattern) (guard : d8112 p = 1) : d2929 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2929, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47185 p hg
    simpa only [d8112, d2929, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2929, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46960 p hg
    simpa only [d8112, d2929, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47383 (p : Pattern) (guard : d8117 p = 1) : d2932 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2932, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46964 p hg
    simpa only [d8117, d2932, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2932, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2932, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47384 (p : Pattern) (guard : d8118 p = 1) : d2933 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2933, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47382 p hg
    simpa only [d8118, d2933, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2933, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47383 p hg
    simpa only [d8118, d2933, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47385 (p : Pattern) (guard : d8119 p = 1) : d2934 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2934, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47381 p hg
    simpa only [d8119, d2934, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2934, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47384 p hg
    simpa only [d8119, d2934, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47386 (p : Pattern) (guard : d8100 p = 1) : d2906 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2906, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35464 p hg
    simpa only [d8100, d2906, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2906, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38955 p hg
    simpa only [d8100, d2906, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47387 (p : Pattern) (guard : d8106 p = 1) : d2908 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2908, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47386 p hg
    simpa only [d8106, d2908, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2908, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38732 p hg
    simpa only [d8106, d2908, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47388 (p : Pattern) (guard : d8111 p = 1) : d2936 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2936, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47213 p hg
    simpa only [d8111, d2936, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2936, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2936, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47389 (p : Pattern) (guard : d8112 p = 1) : d2937 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2937, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47387 p hg
    simpa only [d8112, d2937, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2937, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47388 p hg
    simpa only [d8112, d2937, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47390 (p : Pattern) (guard : d8118 p = 1) : d2939 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2939, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47389 p hg
    simpa only [d8118, d2939, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2939, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46700 p hg
    simpa only [d8118, d2939, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47391 (p : Pattern) (guard : d8124 p = 1) : d2945 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2945, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47390 p hg
    simpa only [d8124, d2945, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2945, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d8124, d2945, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47392 (p : Pattern) (guard : d8125 p = 1) : d2946 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2946, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47385 p hg
    simpa only [d8125, d2946, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2946, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47391 p hg
    simpa only [d8125, d2946, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47393 (p : Pattern) (guard : d8126 p = 1) : d2947 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2947, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47368 p hg
    simpa only [d8126, d2947, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2947, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47392 p hg
    simpa only [d8126, d2947, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47394 (p : Pattern) (guard : d8132 p = 1) : d2979 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2979, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47393 p hg
    simpa only [d8132, d2979, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2979, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47244 p hg
    simpa only [d8132, d2979, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47395 (p : Pattern) (guard : d8107 p = 1) : d2952 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2952, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47257 p hg
    simpa only [d8107, d2952, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2952, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47234 p hg
    simpa only [d8107, d2952, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47396 (p : Pattern) (guard : d8106 p = 1) : d2953 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2953, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47386 p hg
    simpa only [d8106, d2953, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2953, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38956 p hg
    simpa only [d8106, d2953, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47397 (p : Pattern) (guard : d8112 p = 1) : d2955 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2955, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47396 p hg
    simpa only [d8112, d2955, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2955, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47239 p hg
    simpa only [d8112, d2955, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47398 (p : Pattern) (guard : d8113 p = 1) : d2956 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2956, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47395 p hg
    simpa only [d8113, d2956, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2956, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47397 p hg
    simpa only [d8113, d2956, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47399 (p : Pattern) (guard : d8118 p = 1) : d2959 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2959, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47225 p hg
    simpa only [d8118, d2959, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2959, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46722 p hg
    simpa only [d8118, d2959, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47400 (p : Pattern) (guard : d8119 p = 1) : d2960 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2960, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47398 p hg
    simpa only [d8119, d2960, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2960, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47399 p hg
    simpa only [d8119, d2960, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47401 (p : Pattern) (guard : d8112 p = 1) : d2964 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2964, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46627 p hg
    simpa only [d8112, d2964, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2964, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46726 p hg
    simpa only [d8112, d2964, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47402 (p : Pattern) (guard : d8118 p = 1) : d2965 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2965, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47401 p hg
    simpa only [d8118, d2965, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2965, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46515 p hg
    simpa only [d8118, d2965, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47403 (p : Pattern) (guard : d8124 p = 1) : d2966 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2966, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47402 p hg
    simpa only [d8124, d2966, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2966, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2966, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47404 (p : Pattern) (guard : d8125 p = 1) : d2967 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2967, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47400 p hg
    simpa only [d8125, d2967, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2967, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47403 p hg
    simpa only [d8125, d2967, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47405 (p : Pattern) (guard : d8100 p = 1) : d2950 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2950, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35511 p hg
    simpa only [d8100, d2950, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2950, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46714 p hg
    simpa only [d8100, d2950, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47406 (p : Pattern) (guard : d8106 p = 1) : d2951 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2951, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47405 p hg
    simpa only [d8106, d2951, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2951, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38951 p hg
    simpa only [d8106, d2951, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47407 (p : Pattern) (guard : d8105 p = 1) : d2935 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2935, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35517 p hg
    simpa only [d8105, d2935, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2935, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23928 p hg
    simpa only [d8105, d2935, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47408 (p : Pattern) (guard : d8111 p = 1) : d2961 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2961, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47407 p hg
    simpa only [d8111, d2961, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2961, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15281 p hg
    simpa only [d8111, d2961, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47409 (p : Pattern) (guard : d8112 p = 1) : d2968 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2968, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47406 p hg
    simpa only [d8112, d2968, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2968, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47408 p hg
    simpa only [d8112, d2968, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47410 (p : Pattern) (guard : d8105 p = 1) : d2911 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2911, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35524 p hg
    simpa only [d8105, d2911, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2911, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23897 p hg
    simpa only [d8105, d2911, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47411 (p : Pattern) (guard : d8111 p = 1) : d2954 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2954, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47410 p hg
    simpa only [d8111, d2954, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2954, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15333 p hg
    simpa only [d8111, d2954, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47412 (p : Pattern) (guard : d8117 p = 1) : d2969 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2969, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47411 p hg
    simpa only [d8117, d2969, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2969, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46735 p hg
    simpa only [d8117, d2969, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47413 (p : Pattern) (guard : d8118 p = 1) : d2970 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2970, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47409 p hg
    simpa only [d8118, d2970, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2970, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47412 p hg
    simpa only [d8118, d2970, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47414 (p : Pattern) (guard : d8117 p = 1) : d2971 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2971, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47239 p hg
    simpa only [d8117, d2971, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2971, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46738 p hg
    simpa only [d8117, d2971, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47415 (p : Pattern) (guard : d8123 p = 1) : d2972 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2972, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47414 p hg
    simpa only [d8123, d2972, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2972, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46740 p hg
    simpa only [d8123, d2972, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47416 (p : Pattern) (guard : d8124 p = 1) : d2973 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2973, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47413 p hg
    simpa only [d8124, d2973, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2973, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47415 p hg
    simpa only [d8124, d2973, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47417 (p : Pattern) (guard : d8130 p = 1) : d2977 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2977, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47416 p hg
    simpa only [d8130, d2977, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2977, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46745 p hg
    simpa only [d8130, d2977, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47418 (p : Pattern) (guard : d8131 p = 1) : d2978 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2978, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47404 p hg
    simpa only [d8131, d2978, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2978, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47417 p hg
    simpa only [d8131, d2978, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47419 (p : Pattern) (guard : d8106 p = 1) : d2957 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2957, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46795 p hg
    simpa only [d8106, d2957, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2957, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38558 p hg
    simpa only [d8106, d2957, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47420 (p : Pattern) (guard : d8112 p = 1) : d2980 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2980, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47419 p hg
    simpa only [d8112, d2980, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2980, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46514 p hg
    simpa only [d8112, d2980, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47421 (p : Pattern) (guard : d8118 p = 1) : d2981 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2981, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47420 p hg
    simpa only [d8118, d2981, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2981, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46515 p hg
    simpa only [d8118, d2981, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47422 (p : Pattern) (guard : d8124 p = 1) : d2983 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2983, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47421 p hg
    simpa only [d8124, d2983, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2983, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47248 p hg
    simpa only [d8124, d2983, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47423 (p : Pattern) (guard : d8130 p = 1) : d2985 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2985, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47422 p hg
    simpa only [d8130, d2985, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2985, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47250 p hg
    simpa only [d8130, d2985, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47424 (p : Pattern) (guard : d8123 p = 1) : d2982 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2982, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47383 p hg
    simpa only [d8123, d2982, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2982, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2982, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47425 (p : Pattern) (guard : d8129 p = 1) : d2984 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2984, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47424 p hg
    simpa only [d8129, d2984, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2984, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2984, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47426 (p : Pattern) (guard : d8135 p = 1) : d2986 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2986, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47425 p hg
    simpa only [d8135, d2986, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2986, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d2986, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47427 (p : Pattern) (guard : d8136 p = 1) : d2987 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2987, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47423 p hg
    simpa only [d8136, d2987, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2987, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47426 p hg
    simpa only [d8136, d2987, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47428 (p : Pattern) (guard : d8137 p = 1) : d2988 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2988, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47418 p hg
    simpa only [d8137, d2988, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2988, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47427 p hg
    simpa only [d8137, d2988, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47429 (p : Pattern) (guard : d8138 p = 1) : d2989 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d2989, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47394 p hg
    simpa only [d8138, d2989, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d2989, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47428 p hg
    simpa only [d8138, d2989, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47430 (p : Pattern) (guard : d8100 p = 1) : d2895 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2895, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35511 p hg
    simpa only [d8100, d2895, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2895, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39518 p hg
    simpa only [d8100, d2895, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47431 (p : Pattern) (guard : d8106 p = 1) : d2896 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2896, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47430 p hg
    simpa only [d8106, d2896, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2896, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39688 p hg
    simpa only [d8106, d2896, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47432 (p : Pattern) (guard : d8107 p = 1) : d2896 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47180 p hg
    simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47431 p hg
    simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47433 (p : Pattern) (guard : d8100 p = 1) : d2895 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2895, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35482 p hg
    simpa only [d8100, d2895, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2895, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39518 p hg
    simpa only [d8100, d2895, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47434 (p : Pattern) (guard : d8106 p = 1) : d2896 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2896, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47433 p hg
    simpa only [d8106, d2896, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2896, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39688 p hg
    simpa only [d8106, d2896, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47435 (p : Pattern) (guard : d8105 p = 1) : d2897 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2897, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35524 p hg
    simpa only [d8105, d2897, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2897, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23880 p hg
    simpa only [d8105, d2897, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47436 (p : Pattern) (guard : d8111 p = 1) : d2898 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2898, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47435 p hg
    simpa only [d8111, d2898, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2898, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15269 p hg
    simpa only [d8111, d2898, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47437 (p : Pattern) (guard : d8112 p = 1) : d2899 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2899, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47434 p hg
    simpa only [d8112, d2899, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2899, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47436 p hg
    simpa only [d8112, d2899, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47438 (p : Pattern) (guard : d8113 p = 1) : d2900 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2900, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47432 p hg
    simpa only [d8113, d2900, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2900, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47437 p hg
    simpa only [d8113, d2900, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47439 (p : Pattern) (guard : d8100 p = 1) : d2895 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2895, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35464 p hg
    simpa only [d8100, d2895, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2895, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39518 p hg
    simpa only [d8100, d2895, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47440 (p : Pattern) (guard : d8106 p = 1) : d2896 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2896, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47439 p hg
    simpa only [d8106, d2896, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2896, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39688 p hg
    simpa only [d8106, d2896, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47441 (p : Pattern) (guard : d8105 p = 1) : d2897 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2897, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35489 p hg
    simpa only [d8105, d2897, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2897, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23880 p hg
    simpa only [d8105, d2897, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47442 (p : Pattern) (guard : d8111 p = 1) : d2898 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2898, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47441 p hg
    simpa only [d8111, d2898, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2898, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15269 p hg
    simpa only [d8111, d2898, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47443 (p : Pattern) (guard : d8112 p = 1) : d2899 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2899, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47440 p hg
    simpa only [d8112, d2899, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2899, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47442 p hg
    simpa only [d8112, d2899, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47444 (p : Pattern) (guard : d8117 p = 1) : d2903 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46690 p hg
    simpa only [d8117, d2903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47445 (p : Pattern) (guard : d8118 p = 1) : d2904 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2904, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47443 p hg
    simpa only [d8118, d2904, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2904, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47444 p hg
    simpa only [d8118, d2904, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47446 (p : Pattern) (guard : d8119 p = 1) : d2905 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2905, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47438 p hg
    simpa only [d8119, d2905, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2905, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47445 p hg
    simpa only [d8119, d2905, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47447 (p : Pattern) (guard : d8106 p = 1) : d2907 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2907, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47195 p hg
    simpa only [d8106, d2907, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2907, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38742 p hg
    simpa only [d8106, d2907, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47448 (p : Pattern) (guard : d8111 p = 1) : d2908 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47306 p hg
    simpa only [d8111, d2908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15283 p hg
    simpa only [d8111, d2908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47449 (p : Pattern) (guard : d8112 p = 1) : d2909 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2909, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47447 p hg
    simpa only [d8112, d2909, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2909, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47448 p hg
    simpa only [d8112, d2909, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47450 (p : Pattern) (guard : d8111 p = 1) : d2910 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47306 p hg
    simpa only [d8111, d2910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15286 p hg
    simpa only [d8111, d2910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47451 (p : Pattern) (guard : d8117 p = 1) : d2913 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47450 p hg
    simpa only [d8117, d2913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47296 p hg
    simpa only [d8117, d2913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47452 (p : Pattern) (guard : d8118 p = 1) : d2914 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2914, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47449 p hg
    simpa only [d8118, d2914, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2914, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47451 p hg
    simpa only [d8118, d2914, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47453 (p : Pattern) (guard : d8111 p = 1) : d2915 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47306 p hg
    simpa only [d8111, d2915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47454 (p : Pattern) (guard : d8117 p = 1) : d2916 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47453 p hg
    simpa only [d8117, d2916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47296 p hg
    simpa only [d8117, d2916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47455 (p : Pattern) (guard : d0 p = 1) : d2918 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47456 (p : Pattern) (guard : d8123 p = 1) : d2919 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47454 p hg
    simpa only [d8123, d2919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47455 p hg
    simpa only [d8123, d2919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47457 (p : Pattern) (guard : d8124 p = 1) : d2920 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2920, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47452 p hg
    simpa only [d8124, d2920, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2920, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47456 p hg
    simpa only [d8124, d2920, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47458 (p : Pattern) (guard : d8125 p = 1) : d2921 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2921, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47446 p hg
    simpa only [d8125, d2921, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2921, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47457 p hg
    simpa only [d8125, d2921, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47459 (p : Pattern) (guard : d8100 p = 1) : d2895 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35651 p hg
    simpa only [d8100, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39518 p hg
    simpa only [d8100, d2895, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
