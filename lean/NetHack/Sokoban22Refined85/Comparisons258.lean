/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons257
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare36120 (p : Pattern) (guard : d8086 p = 1) : d13 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36119 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35990 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36121 (p : Pattern) (guard : d8091 p = 1) : d3582 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3582, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36120 p hg
    simpa only [d8091, d3582, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3582, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35996 p hg
    simpa only [d8091, d3582, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36122 (p : Pattern) (guard : d8096 p = 1) : d3595 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3595, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36121 p hg
    simpa only [d8096, d3595, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3595, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36004 p hg
    simpa only [d8096, d3595, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36123 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1533 p hg
    simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36124 (p : Pattern) (guard : d8085 p = 1) : d30 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36123 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36056 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36125 (p : Pattern) (guard : d5847 p = 1) : d30 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36126 (p : Pattern) (guard : d8089 p = 1) : d30 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36056 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36125 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36127 (p : Pattern) (guard : d8090 p = 1) : d30 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36124 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36126 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36128 (p : Pattern) (guard : d5847 p = 1) : d3583 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d5847, d3583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5847, d3583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36129 (p : Pattern) (guard : d8089 p = 1) : d3584 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36056 p hg
    simpa only [d8089, d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36128 p hg
    simpa only [d8089, d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36130 (p : Pattern) (guard : d5854 p = 1) : d3586 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36061 p hg
    simpa only [d5854, d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17126 p hg
    simpa only [d5854, d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36131 (p : Pattern) (guard : d8094 p = 1) : d3587 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36129 p hg
    simpa only [d8094, d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36130 p hg
    simpa only [d8094, d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36132 (p : Pattern) (guard : d8095 p = 1) : d3643 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36127 p hg
    simpa only [d8095, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36131 p hg
    simpa only [d8095, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36133 (p : Pattern) (guard : d8101 p = 1) : d3644 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3644, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36132 p hg
    simpa only [d8101, d3644, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3644, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d3644, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36134 (p : Pattern) (guard : d8102 p = 1) : d3645 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3645, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36122 p hg
    simpa only [d8102, d3645, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3645, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36133 p hg
    simpa only [d8102, d3645, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36135 (p : Pattern) (guard : d5854 p = 1) : d23 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36031 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36136 (p : Pattern) (guard : d8094 p = 1) : d23 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36032 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36135 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36137 (p : Pattern) (guard : d5854 p = 1) : d3566 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36031 p hg
    simpa only [d5854, d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17230 p hg
    simpa only [d5854, d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36138 (p : Pattern) (guard : d8099 p = 1) : d3567 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36137 p hg
    simpa only [d8099, d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17230 p hg
    simpa only [d8099, d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36139 (p : Pattern) (guard : d8100 p = 1) : d3568 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36136 p hg
    simpa only [d8100, d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36138 p hg
    simpa only [d8100, d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36140 (p : Pattern) (guard : d8106 p = 1) : d3611 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36139 p hg
    simpa only [d8106, d3611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36141 (p : Pattern) (guard : d8107 p = 1) : d3646 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36024 p hg
    simpa only [d8107, d3646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36140 p hg
    simpa only [d8107, d3646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36142 (p : Pattern) (guard : d8108 p = 1) : d3647 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3647, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36134 p hg
    simpa only [d8108, d3647, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3647, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36141 p hg
    simpa only [d8108, d3647, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36143 (p : Pattern) (guard : d5854 p = 1) : d57 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36092 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36144 (p : Pattern) (guard : d8094 p = 1) : d57 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36093 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36143 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36145 (p : Pattern) (guard : d5854 p = 1) : d3632 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36092 p hg
    simpa only [d5854, d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17174 p hg
    simpa only [d5854, d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36146 (p : Pattern) (guard : d8099 p = 1) : d3633 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36145 p hg
    simpa only [d8099, d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17174 p hg
    simpa only [d8099, d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36147 (p : Pattern) (guard : d8100 p = 1) : d3634 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36144 p hg
    simpa only [d8100, d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36146 p hg
    simpa only [d8100, d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36148 (p : Pattern) (guard : d8106 p = 1) : d3648 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36147 p hg
    simpa only [d8106, d3648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36149 (p : Pattern) (guard : d8107 p = 1) : d3649 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36024 p hg
    simpa only [d8107, d3649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36148 p hg
    simpa only [d8107, d3649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36150 (p : Pattern) (guard : d5854 p = 1) : d39 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36107 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36151 (p : Pattern) (guard : d8094 p = 1) : d39 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36108 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36150 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36152 (p : Pattern) (guard : d5854 p = 1) : d3597 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36107 p hg
    simpa only [d5854, d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17139 p hg
    simpa only [d5854, d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36153 (p : Pattern) (guard : d8099 p = 1) : d3598 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36152 p hg
    simpa only [d8099, d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17139 p hg
    simpa only [d8099, d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36154 (p : Pattern) (guard : d8100 p = 1) : d3638 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36151 p hg
    simpa only [d8100, d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36153 p hg
    simpa only [d8100, d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36155 (p : Pattern) (guard : d8106 p = 1) : d3650 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36154 p hg
    simpa only [d8106, d3650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36156 (p : Pattern) (guard : d8112 p = 1) : d3651 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36155 p hg
    simpa only [d8112, d3651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36157 (p : Pattern) (guard : d8113 p = 1) : d3652 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36149 p hg
    simpa only [d8113, d3652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36156 p hg
    simpa only [d8113, d3652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36158 (p : Pattern) (guard : d8114 p = 1) : d3653 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3653, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36142 p hg
    simpa only [d8114, d3653, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3653, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36157 p hg
    simpa only [d8114, d3653, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36159 (p : Pattern) (guard : d8115 p = 1) : d3654 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d3654, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36118 p hg
    simpa only [d8115, d3654, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d3654, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36158 p hg
    simpa only [d8115, d3654, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36160 (p : Pattern) (guard : d8116 p = 1) : d3655 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8110 p = 1 := by simpa only [d8116, d3655, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36042 p hg
    simpa only [d8116, d3655, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8115 p = 1 := by simpa only [d8116, d3655, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36159 p hg
    simpa only [d8116, d3655, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36161 (p : Pattern) (guard : d8085 p = 1) : d3656 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35874 p hg
    simpa only [d8085, d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35992 p hg
    simpa only [d8085, d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36162 (p : Pattern) (guard : d8086 p = 1) : d3657 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35974 p hg
    simpa only [d8086, d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36161 p hg
    simpa only [d8086, d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36163 (p : Pattern) (guard : d8087 p = 1) : d3658 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d3658, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35935 p hg
    simpa only [d8087, d3658, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d3658, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36162 p hg
    simpa only [d8087, d3658, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36164 (p : Pattern) (guard : d8091 p = 1) : d3659 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35906 p hg
    simpa only [d8091, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36165 (p : Pattern) (guard : d8092 p = 1) : d3660 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3660, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36163 p hg
    simpa only [d8092, d3660, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3660, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36164 p hg
    simpa only [d8092, d3660, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36166 (p : Pattern) (guard : d5847 p = 1) : d3661 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d5847, d3661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5847, d3661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36167 (p : Pattern) (guard : d8089 p = 1) : d3662 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35890 p hg
    simpa only [d8089, d3662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36166 p hg
    simpa only [d8089, d3662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36168 (p : Pattern) (guard : d8090 p = 1) : d3663 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35993 p hg
    simpa only [d8090, d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36167 p hg
    simpa only [d8090, d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36169 (p : Pattern) (guard : d8095 p = 1) : d3664 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36168 p hg
    simpa only [d8095, d3664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36170 (p : Pattern) (guard : d8096 p = 1) : d3665 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3665, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36121 p hg
    simpa only [d8096, d3665, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3665, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36169 p hg
    simpa only [d8096, d3665, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36171 (p : Pattern) (guard : d8097 p = 1) : d3666 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d3666, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36165 p hg
    simpa only [d8097, d3666, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d3666, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36170 p hg
    simpa only [d8097, d3666, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36172 (p : Pattern) (guard : d8095 p = 1) : d3667 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35996 p hg
    simpa only [d8095, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36173 (p : Pattern) (guard : d8096 p = 1) : d3668 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3668, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35997 p hg
    simpa only [d8096, d3668, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3668, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36172 p hg
    simpa only [d8096, d3668, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36174 (p : Pattern) (guard : d8100 p = 1) : d3669 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36022 p hg
    simpa only [d8100, d3669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36175 (p : Pattern) (guard : d8101 p = 1) : d3670 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36023 p hg
    simpa only [d8101, d3670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36174 p hg
    simpa only [d8101, d3670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36176 (p : Pattern) (guard : d8102 p = 1) : d3671 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3671, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36173 p hg
    simpa only [d8102, d3671, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3671, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36175 p hg
    simpa only [d8102, d3671, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36177 (p : Pattern) (guard : d8103 p = 1) : d3672 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3672, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36171 p hg
    simpa only [d8103, d3672, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3672, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36176 p hg
    simpa only [d8103, d3672, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36178 (p : Pattern) (guard : d8096 p = 1) : d3668 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3668, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36008 p hg
    simpa only [d8096, d3668, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3668, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36172 p hg
    simpa only [d8096, d3668, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36179 (p : Pattern) (guard : d8102 p = 1) : d3671 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3671, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36178 p hg
    simpa only [d8102, d3671, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3671, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36175 p hg
    simpa only [d8102, d3671, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36180 (p : Pattern) (guard : d8100 p = 1) : d3673 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36036 p hg
    simpa only [d8100, d3673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36181 (p : Pattern) (guard : d8101 p = 1) : d3674 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36037 p hg
    simpa only [d8101, d3674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36180 p hg
    simpa only [d8101, d3674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36182 (p : Pattern) (guard : d8107 p = 1) : d3675 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36181 p hg
    simpa only [d8107, d3675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d3675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36183 (p : Pattern) (guard : d8108 p = 1) : d3676 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3676, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36179 p hg
    simpa only [d8108, d3676, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3676, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36182 p hg
    simpa only [d8108, d3676, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36184 (p : Pattern) (guard : d8109 p = 1) : d3677 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d3677, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36177 p hg
    simpa only [d8109, d3677, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d3677, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36183 p hg
    simpa only [d8109, d3677, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36185 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36123 p hg
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36186 (p : Pattern) (guard : d8086 p = 1) : d30 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36185 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36057 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36187 (p : Pattern) (guard : d8084 p = 1) : d3583 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d8084, d3583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35917 p hg
    simpa only [d8084, d3583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36188 (p : Pattern) (guard : d8085 p = 1) : d3584 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d8085, d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36187 p hg
    simpa only [d8085, d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36189 (p : Pattern) (guard : d5847 p = 1) : d1715 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d5847, d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36190 (p : Pattern) (guard : d8089 p = 1) : d3586 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36059 p hg
    simpa only [d8089, d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36189 p hg
    simpa only [d8089, d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36191 (p : Pattern) (guard : d8090 p = 1) : d3587 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36188 p hg
    simpa only [d8090, d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36190 p hg
    simpa only [d8090, d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36192 (p : Pattern) (guard : d8091 p = 1) : d3643 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36186 p hg
    simpa only [d8091, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36191 p hg
    simpa only [d8091, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36193 (p : Pattern) (guard : d8095 p = 1) : d3588 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36191 p hg
    simpa only [d8095, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36194 (p : Pattern) (guard : d8096 p = 1) : d3678 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36192 p hg
    simpa only [d8096, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36193 p hg
    simpa only [d8096, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36195 (p : Pattern) (guard : d8084 p = 1) : d34 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34420 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36196 (p : Pattern) (guard : d8085 p = 1) : d34 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36195 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36197 (p : Pattern) (guard : d5847 p = 1) : d34 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34420 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36198 (p : Pattern) (guard : d8089 p = 1) : d34 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36195 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36197 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36199 (p : Pattern) (guard : d8090 p = 1) : d34 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36196 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36198 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36200 (p : Pattern) (guard : d8089 p = 1) : d3590 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36195 p hg
    simpa only [d8089, d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36001 p hg
    simpa only [d8089, d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36201 (p : Pattern) (guard : d5847 p = 1) : d3591 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34420 p hg
    simpa only [d5847, d3591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d3591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36202 (p : Pattern) (guard : d5854 p = 1) : d3592 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36201 p hg
    simpa only [d5854, d3592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17131 p hg
    simpa only [d5854, d3592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36203 (p : Pattern) (guard : d8094 p = 1) : d3593 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36200 p hg
    simpa only [d8094, d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36202 p hg
    simpa only [d8094, d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36204 (p : Pattern) (guard : d8095 p = 1) : d3679 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36199 p hg
    simpa only [d8095, d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36203 p hg
    simpa only [d8095, d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36205 (p : Pattern) (guard : d8100 p = 1) : d3594 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36203 p hg
    simpa only [d8100, d3594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36206 (p : Pattern) (guard : d8101 p = 1) : d3680 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36204 p hg
    simpa only [d8101, d3680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36205 p hg
    simpa only [d8101, d3680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36207 (p : Pattern) (guard : d8102 p = 1) : d3681 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3681, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36194 p hg
    simpa only [d8102, d3681, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3681, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36206 p hg
    simpa only [d8102, d3681, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36208 (p : Pattern) (guard : d8085 p = 1) : d39 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare710 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36105 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36209 (p : Pattern) (guard : d8090 p = 1) : d39 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36208 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36108 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36210 (p : Pattern) (guard : d8095 p = 1) : d3638 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36209 p hg
    simpa only [d8095, d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36112 p hg
    simpa only [d8095, d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36211 (p : Pattern) (guard : d8101 p = 1) : d3639 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36210 p hg
    simpa only [d8101, d3639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36114 p hg
    simpa only [d8101, d3639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36212 (p : Pattern) (guard : d8107 p = 1) : d3640 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36211 p hg
    simpa only [d8107, d3640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d3640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36213 (p : Pattern) (guard : d8108 p = 1) : d3682 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3682, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36207 p hg
    simpa only [d8108, d3682, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3682, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36212 p hg
    simpa only [d8108, d3682, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36214 (p : Pattern) (guard : d8114 p = 1) : d3683 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3683, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36213 p hg
    simpa only [d8114, d3683, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3683, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d3683, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36215 (p : Pattern) (guard : d8115 p = 1) : d3684 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d3684, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36184 p hg
    simpa only [d8115, d3684, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d3684, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36214 p hg
    simpa only [d8115, d3684, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36216 (p : Pattern) (guard : d8086 p = 1) : d13 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35872 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35990 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36217 (p : Pattern) (guard : d8091 p = 1) : d3582 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3582, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36216 p hg
    simpa only [d8091, d3582, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3582, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35996 p hg
    simpa only [d8091, d3582, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36218 (p : Pattern) (guard : d8096 p = 1) : d3665 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3665, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36217 p hg
    simpa only [d8096, d3665, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3665, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36169 p hg
    simpa only [d8096, d3665, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36219 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34583 p hg
    simpa only [d30, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d30, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36220 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36219 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36221 (p : Pattern) (guard : d8085 p = 1) : d30 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36220 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36056 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36222 (p : Pattern) (guard : d8090 p = 1) : d30 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36221 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36126 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36223 (p : Pattern) (guard : d8095 p = 1) : d3643 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36222 p hg
    simpa only [d8095, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36131 p hg
    simpa only [d8095, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36224 (p : Pattern) (guard : d8100 p = 1) : d3588 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36131 p hg
    simpa only [d8100, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36225 (p : Pattern) (guard : d8101 p = 1) : d3678 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36223 p hg
    simpa only [d8101, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36224 p hg
    simpa only [d8101, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36226 (p : Pattern) (guard : d8102 p = 1) : d3685 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3685, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36218 p hg
    simpa only [d8102, d3685, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3685, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36225 p hg
    simpa only [d8102, d3685, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36227 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare938 p hg
    simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36228 (p : Pattern) (guard : d8085 p = 1) : d17 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36227 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35914 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36229 (p : Pattern) (guard : d8090 p = 1) : d17 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36228 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36017 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36230 (p : Pattern) (guard : d8095 p = 1) : d3605 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3605, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36229 p hg
    simpa only [d8095, d3605, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3605, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36022 p hg
    simpa only [d8095, d3605, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36231 (p : Pattern) (guard : d8101 p = 1) : d3670 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3670, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36230 p hg
    simpa only [d8101, d3670, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3670, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36174 p hg
    simpa only [d8101, d3670, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36232 (p : Pattern) (guard : d8105 p = 1) : d3673 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36138 p hg
    simpa only [d8105, d3673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36233 (p : Pattern) (guard : d8106 p = 1) : d3674 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36139 p hg
    simpa only [d8106, d3674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36232 p hg
    simpa only [d8106, d3674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36234 (p : Pattern) (guard : d8107 p = 1) : d3686 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3686, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36231 p hg
    simpa only [d8107, d3686, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3686, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36233 p hg
    simpa only [d8107, d3686, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36235 (p : Pattern) (guard : d8108 p = 1) : d3687 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3687, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36226 p hg
    simpa only [d8108, d3687, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3687, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36234 p hg
    simpa only [d8108, d3687, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36236 (p : Pattern) (guard : d8105 p = 1) : d3635 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36146 p hg
    simpa only [d8105, d3635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36237 (p : Pattern) (guard : d8106 p = 1) : d3636 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36147 p hg
    simpa only [d8106, d3636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36236 p hg
    simpa only [d8106, d3636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36238 (p : Pattern) (guard : d8107 p = 1) : d3688 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36175 p hg
    simpa only [d8107, d3688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36237 p hg
    simpa only [d8107, d3688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36239 (p : Pattern) (guard : d8105 p = 1) : d3599 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36153 p hg
    simpa only [d8105, d3599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36240 (p : Pattern) (guard : d8106 p = 1) : d3639 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36154 p hg
    simpa only [d8106, d3639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36239 p hg
    simpa only [d8106, d3639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36241 (p : Pattern) (guard : d8112 p = 1) : d3640 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36240 p hg
    simpa only [d8112, d3640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36242 (p : Pattern) (guard : d8113 p = 1) : d3689 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36238 p hg
    simpa only [d8113, d3689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36241 p hg
    simpa only [d8113, d3689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36243 (p : Pattern) (guard : d8114 p = 1) : d3690 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3690, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36235 p hg
    simpa only [d8114, d3690, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3690, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36242 p hg
    simpa only [d8114, d3690, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36244 (p : Pattern) (guard : d8107 p = 1) : d3691 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36206 p hg
    simpa only [d8107, d3691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d3691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36245 (p : Pattern) (guard : d8113 p = 1) : d3692 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36244 p hg
    simpa only [d8113, d3692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d3692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36246 (p : Pattern) (guard : d8119 p = 1) : d3693 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36245 p hg
    simpa only [d8119, d3693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d3693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36247 (p : Pattern) (guard : d8120 p = 1) : d3694 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3694, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36243 p hg
    simpa only [d8120, d3694, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3694, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36246 p hg
    simpa only [d8120, d3694, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36248 (p : Pattern) (guard : d8121 p = 1) : d3695 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d3695, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36215 p hg
    simpa only [d8121, d3695, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d3695, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36247 p hg
    simpa only [d8121, d3695, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36249 (p : Pattern) (guard : d8122 p = 1) : d3696 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d3696, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36160 p hg
    simpa only [d8122, d3696, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d3696, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36248 p hg
    simpa only [d8122, d3696, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36250 (p : Pattern) (guard : d8087 p = 1) : d3658 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d3658, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35904 p hg
    simpa only [d8087, d3658, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d3658, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36162 p hg
    simpa only [d8087, d3658, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36251 (p : Pattern) (guard : d8091 p = 1) : d3659 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3659, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35892 p hg
    simpa only [d8091, d3659, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3659, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3659, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36252 (p : Pattern) (guard : d8092 p = 1) : d3660 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3660, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36250 p hg
    simpa only [d8092, d3660, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3660, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36251 p hg
    simpa only [d8092, d3660, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36253 (p : Pattern) (guard : d8097 p = 1) : d3666 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d3666, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36252 p hg
    simpa only [d8097, d3666, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d3666, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36218 p hg
    simpa only [d8097, d3666, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36254 (p : Pattern) (guard : d8096 p = 1) : d3668 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3668, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36121 p hg
    simpa only [d8096, d3668, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3668, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36172 p hg
    simpa only [d8096, d3668, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36255 (p : Pattern) (guard : d8102 p = 1) : d3671 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3671, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36254 p hg
    simpa only [d8102, d3671, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3671, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36231 p hg
    simpa only [d8102, d3671, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36256 (p : Pattern) (guard : d8103 p = 1) : d3672 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3672, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36253 p hg
    simpa only [d8103, d3672, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3672, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36255 p hg
    simpa only [d8103, d3672, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36257 (p : Pattern) (guard : d8108 p = 1) : d3676 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3676, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36176 p hg
    simpa only [d8108, d3676, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3676, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36182 p hg
    simpa only [d8108, d3676, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36258 (p : Pattern) (guard : d8109 p = 1) : d3677 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d3677, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36256 p hg
    simpa only [d8109, d3677, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d3677, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36257 p hg
    simpa only [d8109, d3677, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36259 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36220 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
