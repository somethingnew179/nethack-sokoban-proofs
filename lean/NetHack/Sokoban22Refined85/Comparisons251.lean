/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons250
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare35140 (p : Pattern) (guard : d8106 p = 1) : d109 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d109, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35138 p hg
    simpa only [d8106, d109, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d109, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35139 p hg
    simpa only [d8106, d109, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35141 (p : Pattern) (guard : d8107 p = 1) : d110 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d110, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35127 p hg
    simpa only [d8107, d110, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d110, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35140 p hg
    simpa only [d8107, d110, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35142 (p : Pattern) (guard : d8108 p = 1) : d111 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d111, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35120 p hg
    simpa only [d8108, d111, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d111, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35141 p hg
    simpa only [d8108, d111, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35143 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d6 p := by
  change (1 : Int) ≤ (0 : Int) + 6
  decide
theorem compare35144 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35143 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35145 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35144 p hg
    simpa only [d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35146 (p : Pattern) (guard : d8085 p = 1) : d103 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35145 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35094 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35147 (p : Pattern) (guard : d8090 p = 1) : d103 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35146 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35100 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35148 (p : Pattern) (guard : d8095 p = 1) : d103 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35147 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35115 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35149 (p : Pattern) (guard : d8101 p = 1) : d105 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d105, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35148 p hg
    simpa only [d8101, d105, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d105, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35126 p hg
    simpa only [d8101, d105, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35150 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1421 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1319 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35151 (p : Pattern) (guard : d8084 p = 1) : d107 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d107, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35150 p hg
    simpa only [d8084, d107, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d107, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35130 p hg
    simpa only [d8084, d107, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35152 (p : Pattern) (guard : d8089 p = 1) : d107 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35151 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35133 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35153 (p : Pattern) (guard : d8094 p = 1) : d107 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35152 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35135 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35154 (p : Pattern) (guard : d8100 p = 1) : d107 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35153 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35137 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35155 (p : Pattern) (guard : d8106 p = 1) : d109 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d109, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35154 p hg
    simpa only [d8106, d109, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d109, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35139 p hg
    simpa only [d8106, d109, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35156 (p : Pattern) (guard : d8107 p = 1) : d110 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d110, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35149 p hg
    simpa only [d8107, d110, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d110, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35155 p hg
    simpa only [d8107, d110, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35157 (p : Pattern) (guard : d8112 p = 1) : d112 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34989 p hg
    simpa only [d8112, d112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35158 (p : Pattern) (guard : d8113 p = 1) : d113 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d113, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35156 p hg
    simpa only [d8113, d113, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d113, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35157 p hg
    simpa only [d8113, d113, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35159 (p : Pattern) (guard : d8114 p = 1) : d114 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35142 p hg
    simpa only [d8114, d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35158 p hg
    simpa only [d8114, d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35160 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1403 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35161 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35160 p hg
    simpa only [d103, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d103, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35162 (p : Pattern) (guard : d8085 p = 1) : d103 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35161 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35094 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35163 (p : Pattern) (guard : d8090 p = 1) : d103 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35162 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35100 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35164 (p : Pattern) (guard : d8095 p = 1) : d103 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35163 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35115 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35165 (p : Pattern) (guard : d5843 p = 1) : d115 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35166 (p : Pattern) (guard : d8084 p = 1) : d116 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d8084, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35165 p hg
    simpa only [d8084, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35167 (p : Pattern) (guard : d5843 p = 1) : d3 p ≤ (0 : Int) + d12 p := by
  change (3 : Int) ≤ (0 : Int) + 12
  decide
theorem compare35168 (p : Pattern) (guard : d5847 p = 1) : d116 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35167 p hg
    simpa only [d5847, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35169 (p : Pattern) (guard : d8089 p = 1) : d116 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35166 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35168 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35170 (p : Pattern) (guard : d5854 p = 1) : d116 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35168 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35171 (p : Pattern) (guard : d8094 p = 1) : d116 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35169 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35170 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35172 (p : Pattern) (guard : d8100 p = 1) : d117 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35171 p hg
    simpa only [d8100, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35173 (p : Pattern) (guard : d8101 p = 1) : d118 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d118, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35164 p hg
    simpa only [d8101, d118, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d118, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35172 p hg
    simpa only [d8101, d118, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35174 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1583 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35175 (p : Pattern) (guard : d8084 p = 1) : d103 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d103, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35174 p hg
    simpa only [d8084, d103, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d103, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d103, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35176 (p : Pattern) (guard : d8089 p = 1) : d103 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35175 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35099 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35177 (p : Pattern) (guard : d8094 p = 1) : d103 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35176 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35114 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35178 (p : Pattern) (guard : d8099 p = 1) : d103 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35114 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35179 (p : Pattern) (guard : d8100 p = 1) : d103 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35177 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35178 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35180 (p : Pattern) (guard : d5843 p = 1) : d7 p ≤ (0 : Int) + d12 p := by
  change (7 : Int) ≤ (0 : Int) + 12
  decide
theorem compare35181 (p : Pattern) (guard : d5847 p = 1) : d120 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35180 p hg
    simpa only [d5847, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5847, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35182 (p : Pattern) (guard : d5854 p = 1) : d120 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35181 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11672 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35183 (p : Pattern) (guard : d8099 p = 1) : d120 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35182 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11672 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35184 (p : Pattern) (guard : d8105 p = 1) : d121 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35183 p hg
    simpa only [d8105, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35185 (p : Pattern) (guard : d8106 p = 1) : d122 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d122, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35179 p hg
    simpa only [d8106, d122, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d122, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35184 p hg
    simpa only [d8106, d122, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35186 (p : Pattern) (guard : d8107 p = 1) : d123 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d123, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35173 p hg
    simpa only [d8107, d123, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d123, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35185 p hg
    simpa only [d8107, d123, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35187 (p : Pattern) (guard : d8100 p = 1) : d103 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35117 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35178 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35188 (p : Pattern) (guard : d8106 p = 1) : d124 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d124, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35187 p hg
    simpa only [d8106, d124, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d124, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d124, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35189 (p : Pattern) (guard : d8105 p = 1) : d107 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35137 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35190 (p : Pattern) (guard : d8111 p = 1) : d125 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35189 p hg
    simpa only [d8111, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35191 (p : Pattern) (guard : d8112 p = 1) : d126 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d126, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35188 p hg
    simpa only [d8112, d126, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d126, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35190 p hg
    simpa only [d8112, d126, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35192 (p : Pattern) (guard : d8113 p = 1) : d127 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d127, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35186 p hg
    simpa only [d8113, d127, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d127, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35191 p hg
    simpa only [d8113, d127, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35193 (p : Pattern) (guard : d8100 p = 1) : d103 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35115 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35178 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35194 (p : Pattern) (guard : d8106 p = 1) : d124 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35193 p hg
    simpa only [d8106, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35195 (p : Pattern) (guard : d8112 p = 1) : d126 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35194 p hg
    simpa only [d8112, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35190 p hg
    simpa only [d8112, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35196 (p : Pattern) (guard : d8117 p = 1) : d128 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34687 p hg
    simpa only [d8117, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35197 (p : Pattern) (guard : d8118 p = 1) : d129 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35195 p hg
    simpa only [d8118, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35196 p hg
    simpa only [d8118, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35198 (p : Pattern) (guard : d8119 p = 1) : d130 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d130, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35192 p hg
    simpa only [d8119, d130, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d130, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35197 p hg
    simpa only [d8119, d130, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35199 (p : Pattern) (guard : d8120 p = 1) : d131 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d131, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35159 p hg
    simpa only [d8120, d131, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d131, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35198 p hg
    simpa only [d8120, d131, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35200 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35201 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d326 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35200 p hg
    simpa only [d103, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4579 p hg
    simpa only [d103, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35202 (p : Pattern) (guard : d8085 p = 1) : d103 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35201 p hg
    simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35111 p hg
    simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35203 (p : Pattern) (guard : d8090 p = 1) : d103 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35202 p hg
    simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35176 p hg
    simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35204 (p : Pattern) (guard : d8095 p = 1) : d103 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35203 p hg
    simpa only [d8095, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35117 p hg
    simpa only [d8095, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35205 (p : Pattern) (guard : d8100 p = 1) : d104 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d104, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35177 p hg
    simpa only [d8100, d104, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d104, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d104, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35206 (p : Pattern) (guard : d8101 p = 1) : d105 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d105, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35204 p hg
    simpa only [d8101, d105, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d105, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35205 p hg
    simpa only [d8101, d105, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35207 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d6 p := by
  change (3 : Int) ≤ (0 : Int) + 6
  decide
theorem compare35208 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35207 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35209 (p : Pattern) (guard : d8084 p = 1) : d116 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d116, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35208 p hg
    simpa only [d8084, d116, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d116, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35165 p hg
    simpa only [d8084, d116, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35210 (p : Pattern) (guard : d8089 p = 1) : d116 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35209 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35168 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35211 (p : Pattern) (guard : d8094 p = 1) : d116 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35210 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35170 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35212 (p : Pattern) (guard : d8099 p = 1) : d116 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35170 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35213 (p : Pattern) (guard : d8100 p = 1) : d116 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35211 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35212 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35214 (p : Pattern) (guard : d8105 p = 1) : d117 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35212 p hg
    simpa only [d8105, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35215 (p : Pattern) (guard : d8106 p = 1) : d132 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d132, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35213 p hg
    simpa only [d8106, d132, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d132, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35214 p hg
    simpa only [d8106, d132, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35216 (p : Pattern) (guard : d8107 p = 1) : d133 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d133, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35206 p hg
    simpa only [d8107, d133, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d133, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35215 p hg
    simpa only [d8107, d133, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35217 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1415 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1319 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35218 (p : Pattern) (guard : d8084 p = 1) : d107 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d107, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35217 p hg
    simpa only [d8084, d107, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d107, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35130 p hg
    simpa only [d8084, d107, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35219 (p : Pattern) (guard : d8089 p = 1) : d107 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35218 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35133 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35220 (p : Pattern) (guard : d8094 p = 1) : d107 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35219 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35135 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35221 (p : Pattern) (guard : d8100 p = 1) : d107 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35220 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35137 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35222 (p : Pattern) (guard : d8106 p = 1) : d109 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d109, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35221 p hg
    simpa only [d8106, d109, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d109, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35139 p hg
    simpa only [d8106, d109, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35223 (p : Pattern) (guard : d5854 p = 1) : d58 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19998 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11502 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35224 (p : Pattern) (guard : d8099 p = 1) : d58 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35223 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11502 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35225 (p : Pattern) (guard : d8105 p = 1) : d58 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35224 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11502 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35226 (p : Pattern) (guard : d8111 p = 1) : d60 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d60, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35225 p hg
    simpa only [d8111, d60, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d60, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5081 p hg
    simpa only [d8111, d60, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35227 (p : Pattern) (guard : d8112 p = 1) : d134 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d134, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35222 p hg
    simpa only [d8112, d134, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d134, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35226 p hg
    simpa only [d8112, d134, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35228 (p : Pattern) (guard : d8113 p = 1) : d135 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d135, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35216 p hg
    simpa only [d8113, d135, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d135, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35227 p hg
    simpa only [d8113, d135, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35229 (p : Pattern) (guard : d5854 p = 1) : d40 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19941 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11507 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35230 (p : Pattern) (guard : d8099 p = 1) : d40 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35229 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11507 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35231 (p : Pattern) (guard : d8105 p = 1) : d40 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35230 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11507 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35232 (p : Pattern) (guard : d8111 p = 1) : d62 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d62, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35231 p hg
    simpa only [d8111, d62, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d62, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5067 p hg
    simpa only [d8111, d62, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35233 (p : Pattern) (guard : d8112 p = 1) : d136 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d136, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35140 p hg
    simpa only [d8112, d136, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d136, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35232 p hg
    simpa only [d8112, d136, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35234 (p : Pattern) (guard : d8118 p = 1) : d137 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d137, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35233 p hg
    simpa only [d8118, d137, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d137, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d137, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35235 (p : Pattern) (guard : d8119 p = 1) : d138 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d138, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35228 p hg
    simpa only [d8119, d138, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d138, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35234 p hg
    simpa only [d8119, d138, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35236 (p : Pattern) (guard : d8084 p = 1) : d103 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35087 p hg
    simpa only [d8084, d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35237 (p : Pattern) (guard : d8089 p = 1) : d103 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35236 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35099 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35238 (p : Pattern) (guard : d8094 p = 1) : d103 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35237 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35114 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35239 (p : Pattern) (guard : d8100 p = 1) : d103 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35238 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35178 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35240 (p : Pattern) (guard : d8106 p = 1) : d122 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d122, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35239 p hg
    simpa only [d8106, d122, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d122, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35184 p hg
    simpa only [d8106, d122, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35241 (p : Pattern) (guard : d8105 p = 1) : d116 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35212 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35242 (p : Pattern) (guard : d8111 p = 1) : d139 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35241 p hg
    simpa only [d8111, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35243 (p : Pattern) (guard : d8112 p = 1) : d140 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d140, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35240 p hg
    simpa only [d8112, d140, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d140, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35242 p hg
    simpa only [d8112, d140, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35244 (p : Pattern) (guard : d8117 p = 1) : d141 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35190 p hg
    simpa only [d8117, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34902 p hg
    simpa only [d8117, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35245 (p : Pattern) (guard : d8118 p = 1) : d142 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d142, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35243 p hg
    simpa only [d8118, d142, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d142, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35244 p hg
    simpa only [d8118, d142, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35246 (p : Pattern) (guard : d0 p = 1) : d72 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35247 (p : Pattern) (guard : d8117 p = 1) : d143 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35190 p hg
    simpa only [d8117, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35246 p hg
    simpa only [d8117, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35248 (p : Pattern) (guard : d8123 p = 1) : d144 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35247 p hg
    simpa only [d8123, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35249 (p : Pattern) (guard : d8124 p = 1) : d145 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d145, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35245 p hg
    simpa only [d8124, d145, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d145, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35248 p hg
    simpa only [d8124, d145, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35250 (p : Pattern) (guard : d8125 p = 1) : d146 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d146, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35235 p hg
    simpa only [d8125, d146, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d146, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35249 p hg
    simpa only [d8125, d146, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35251 (p : Pattern) (guard : d8126 p = 1) : d147 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d147, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35199 p hg
    simpa only [d8126, d147, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d147, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35250 p hg
    simpa only [d8126, d147, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35252 (p : Pattern) (guard : d8105 p = 1) : d104 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35178 p hg
    simpa only [d8105, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35253 (p : Pattern) (guard : d8106 p = 1) : d105 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d105, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35239 p hg
    simpa only [d8106, d105, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d105, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35252 p hg
    simpa only [d8106, d105, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35254 (p : Pattern) (guard : d8107 p = 1) : d105 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35149 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35253 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35255 (p : Pattern) (guard : d8106 p = 1) : d105 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d105, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35179 p hg
    simpa only [d8106, d105, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d105, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35252 p hg
    simpa only [d8106, d105, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35256 (p : Pattern) (guard : d8111 p = 1) : d109 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35189 p hg
    simpa only [d8111, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d8111, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35257 (p : Pattern) (guard : d8112 p = 1) : d110 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d110, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35255 p hg
    simpa only [d8112, d110, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d110, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35256 p hg
    simpa only [d8112, d110, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35258 (p : Pattern) (guard : d8113 p = 1) : d111 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d111, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35254 p hg
    simpa only [d8113, d111, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d111, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35257 p hg
    simpa only [d8113, d111, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35259 (p : Pattern) (guard : d8106 p = 1) : d105 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d105, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35187 p hg
    simpa only [d8106, d105, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d105, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35252 p hg
    simpa only [d8106, d105, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35260 (p : Pattern) (guard : d8112 p = 1) : d110 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d110, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35259 p hg
    simpa only [d8112, d110, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d110, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35256 p hg
    simpa only [d8112, d110, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35261 (p : Pattern) (guard : d8117 p = 1) : d112 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34727 p hg
    simpa only [d8117, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35262 (p : Pattern) (guard : d8118 p = 1) : d113 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d113, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35260 p hg
    simpa only [d8118, d113, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d113, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35261 p hg
    simpa only [d8118, d113, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35263 (p : Pattern) (guard : d8119 p = 1) : d114 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d114, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35258 p hg
    simpa only [d8119, d114, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d114, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35262 p hg
    simpa only [d8119, d114, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35264 (p : Pattern) (guard : d8100 p = 1) : d116 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35171 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35212 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35265 (p : Pattern) (guard : d8106 p = 1) : d132 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35264 p hg
    simpa only [d8106, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35214 p hg
    simpa only [d8106, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35266 (p : Pattern) (guard : d8105 p = 1) : d120 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35183 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11672 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35267 (p : Pattern) (guard : d8111 p = 1) : d148 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35266 p hg
    simpa only [d8111, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5173 p hg
    simpa only [d8111, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35268 (p : Pattern) (guard : d8112 p = 1) : d149 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35265 p hg
    simpa only [d8112, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35267 p hg
    simpa only [d8112, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35269 (p : Pattern) (guard : d8118 p = 1) : d150 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35268 p hg
    simpa only [d8118, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35270 (p : Pattern) (guard : d8124 p = 1) : d151 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35269 p hg
    simpa only [d8124, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35271 (p : Pattern) (guard : d8125 p = 1) : d152 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d152, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35263 p hg
    simpa only [d8125, d152, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d152, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35270 p hg
    simpa only [d8125, d152, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35272 (p : Pattern) (guard : d8084 p = 1) : d103 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d103, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35091 p hg
    simpa only [d8084, d103, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d103, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d103, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35273 (p : Pattern) (guard : d8089 p = 1) : d103 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35272 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35099 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35274 (p : Pattern) (guard : d8094 p = 1) : d103 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35273 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35114 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35275 (p : Pattern) (guard : d8100 p = 1) : d103 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35274 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35178 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35276 (p : Pattern) (guard : d8106 p = 1) : d105 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d105, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35275 p hg
    simpa only [d8106, d105, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d105, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35252 p hg
    simpa only [d8106, d105, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35277 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d11 p := by
  change (3 : Int) ≤ (0 : Int) + 11
  decide
theorem compare35278 (p : Pattern) (guard : d5843 p = 1) : d3 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35277 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20196 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35279 (p : Pattern) (guard : d5847 p = 1) : d116 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d116, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35278 p hg
    simpa only [d5847, d116, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d116, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d116, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
