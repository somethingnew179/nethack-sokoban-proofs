/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons043
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6160 (p : Pattern) (guard : d1092 p = 1) : d461 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d461, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6158 p hg
    simpa only [d461, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d461, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6159 p hg
    simpa only [d461, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6161 (p : Pattern) (guard : d1092 p = 1) : d462 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d462, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6157 p hg
    simpa only [d462, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d462, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6160 p hg
    simpa only [d462, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6162 (p : Pattern) (guard : d1092 p = 1) : d58 p ≤ (0 : Int) + d35 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5703 p hg
    simpa only [d1092, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare444 p hg
    simpa only [d1092, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6163 (p : Pattern) (guard : d1092 p = 1) : d463 p ≤ (0 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d463, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6155 p hg
    simpa only [d463, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d463, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6162 p hg
    simpa only [d463, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6164 (p : Pattern) (guard : d1092 p = 1) : d465 p ≤ (0 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d465, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5708 p hg
    simpa only [d1092, d465, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d465, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare447 p hg
    simpa only [d1092, d465, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6165 (p : Pattern) (guard : d1092 p = 1) : d466 p ≤ (0 : Int) + d43 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d466, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6164 p hg
    simpa only [d466, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d466, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6159 p hg
    simpa only [d466, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6166 (p : Pattern) (guard : d1092 p = 1) : d467 p ≤ (0 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d467, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6163 p hg
    simpa only [d467, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d467, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6165 p hg
    simpa only [d467, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6167 (p : Pattern) (guard : d1092 p = 1) : d468 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d468, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6161 p hg
    simpa only [d468, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d468, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6166 p hg
    simpa only [d468, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6168 (p : Pattern) (guard : d1093 p = 1) : d468 p ≤ (0 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5714 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6167 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6169 (p : Pattern) (guard : d1094 p = 1) : d476 p ≤ (0 : Int) + d184 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d476, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6168 p hg
    simpa only [d1094, d476, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d476, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5727 p hg
    simpa only [d1094, d476, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6170 (p : Pattern) (guard : d1092 p = 1) : d484 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d484, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5767 p hg
    simpa only [d1092, d484, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d484, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare438 p hg
    simpa only [d1092, d484, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6171 (p : Pattern) (guard : d1092 p = 1) : d485 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d485, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6170 p hg
    simpa only [d485, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d485, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6159 p hg
    simpa only [d485, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6172 (p : Pattern) (guard : d1092 p = 1) : d486 p ≤ (0 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d486, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6171 p hg
    simpa only [d486, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d486, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1645 p hg
    simpa only [d486, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6173 (p : Pattern) (guard : d1092 p = 1) : d487 p ≤ (0 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d487, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6161 p hg
    simpa only [d487, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d487, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6172 p hg
    simpa only [d487, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6174 (p : Pattern) (guard : d1093 p = 1) : d488 p ≤ (0 : Int) + d78 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, d488, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5738 p hg
    simpa only [d1093, d488, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, d488, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6173 p hg
    simpa only [d1093, d488, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6175 (p : Pattern) (guard : d0 p = 1) : d493 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6176 (p : Pattern) (guard : d1094 p = 1) : d494 p ≤ (0 : Int) + d185 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d494, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6174 p hg
    simpa only [d1094, d494, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d494, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6175 p hg
    simpa only [d1094, d494, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6177 (p : Pattern) (guard : d1094 p = 1) : d495 p ≤ (0 : Int) + d186 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d495, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6169 p hg
    simpa only [d495, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1094 p = 1 := by simpa only [d495, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6176 p hg
    simpa only [d495, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6178 (p : Pattern) (guard : d1092 p = 1) : d457 p ≤ (0 : Int) + d187 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d457, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5684 p hg
    simpa only [d1092, d457, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d457, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5163 p hg
    simpa only [d1092, d457, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6179 (p : Pattern) (guard : d1092 p = 1) : d52 p ≤ (0 : Int) + d187 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5689 p hg
    simpa only [d1092, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5163 p hg
    simpa only [d1092, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6180 (p : Pattern) (guard : d1092 p = 1) : d458 p ≤ (0 : Int) + d187 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6178 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6179 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6181 (p : Pattern) (guard : d1092 p = 1) : d460 p ≤ (0 : Int) + d187 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d460, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5693 p hg
    simpa only [d1092, d460, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d460, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5163 p hg
    simpa only [d1092, d460, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6182 (p : Pattern) (guard : d1092 p = 1) : d54 p ≤ (0 : Int) + d188 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5696 p hg
    simpa only [d1092, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5165 p hg
    simpa only [d1092, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6183 (p : Pattern) (guard : d1092 p = 1) : d461 p ≤ (0 : Int) + d189 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d461, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6181 p hg
    simpa only [d461, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d461, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6182 p hg
    simpa only [d461, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6184 (p : Pattern) (guard : d1092 p = 1) : d462 p ≤ (0 : Int) + d190 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d462, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6180 p hg
    simpa only [d462, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d462, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6183 p hg
    simpa only [d462, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6185 (p : Pattern) (guard : d1092 p = 1) : d484 p ≤ (0 : Int) + d187 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d484, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5767 p hg
    simpa only [d1092, d484, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d484, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5163 p hg
    simpa only [d1092, d484, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6186 (p : Pattern) (guard : d1092 p = 1) : d58 p ≤ (0 : Int) + d191 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5703 p hg
    simpa only [d1092, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5169 p hg
    simpa only [d1092, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6187 (p : Pattern) (guard : d1092 p = 1) : d496 p ≤ (0 : Int) + d192 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d496, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6185 p hg
    simpa only [d496, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d496, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6186 p hg
    simpa only [d496, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6188 (p : Pattern) (guard : d1092 p = 1) : d61 p ≤ (0 : Int) + d193 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5791 p hg
    simpa only [d1092, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5172 p hg
    simpa only [d1092, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6189 (p : Pattern) (guard : d1092 p = 1) : d473 p ≤ (0 : Int) + d194 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d473, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6188 p hg
    simpa only [d473, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d473, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6182 p hg
    simpa only [d473, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6190 (p : Pattern) (guard : d1092 p = 1) : d497 p ≤ (0 : Int) + d195 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d497, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6187 p hg
    simpa only [d497, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d497, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6189 p hg
    simpa only [d497, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6191 (p : Pattern) (guard : d1092 p = 1) : d498 p ≤ (0 : Int) + d196 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d498, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6184 p hg
    simpa only [d498, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d498, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6190 p hg
    simpa only [d498, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6192 (p : Pattern) (guard : d1093 p = 1) : d499 p ≤ (0 : Int) + d197 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, d499, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5714 p hg
    simpa only [d1093, d499, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, d499, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6191 p hg
    simpa only [d1093, d499, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6193 (p : Pattern) (guard : d0 p = 1) : d508 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6194 (p : Pattern) (guard : d1094 p = 1) : d509 p ≤ (0 : Int) + d198 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d509, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6192 p hg
    simpa only [d1094, d509, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d509, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6193 p hg
    simpa only [d1094, d509, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6195 (p : Pattern) (guard : d1092 p = 1) : d510 p ≤ (0 : Int) + d187 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6185 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6179 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6196 (p : Pattern) (guard : d1092 p = 1) : d470 p ≤ (0 : Int) + d189 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d470, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6179 p hg
    simpa only [d470, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d470, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6182 p hg
    simpa only [d470, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6197 (p : Pattern) (guard : d1092 p = 1) : d511 p ≤ (0 : Int) + d190 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d511, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6195 p hg
    simpa only [d511, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d511, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6196 p hg
    simpa only [d511, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6198 (p : Pattern) (guard : d1092 p = 1) : d491 p ≤ (0 : Int) + d202 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d491, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6196 p hg
    simpa only [d491, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d491, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2080 p hg
    simpa only [d491, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6199 (p : Pattern) (guard : d1092 p = 1) : d512 p ≤ (0 : Int) + d203 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d512, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6197 p hg
    simpa only [d512, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d512, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6198 p hg
    simpa only [d512, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6200 (p : Pattern) (guard : d1093 p = 1) : d513 p ≤ (0 : Int) + d204 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, d513, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5771 p hg
    simpa only [d1093, d513, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, d513, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6199 p hg
    simpa only [d1093, d513, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6201 (p : Pattern) (guard : d0 p = 1) : d515 p ≤ (0 : Int) + d164 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6202 (p : Pattern) (guard : d1094 p = 1) : d516 p ≤ (0 : Int) + d205 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d516, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6200 p hg
    simpa only [d1094, d516, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d516, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6201 p hg
    simpa only [d1094, d516, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6203 (p : Pattern) (guard : d1094 p = 1) : d517 p ≤ (0 : Int) + d206 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d517, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6194 p hg
    simpa only [d517, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1094 p = 1 := by simpa only [d517, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6202 p hg
    simpa only [d517, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6204 (p : Pattern) (guard : d1094 p = 1) : d518 p ≤ (0 : Int) + d207 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d518, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6177 p hg
    simpa only [d518, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1094 p = 1 := by simpa only [d518, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6203 p hg
    simpa only [d518, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6205 (p : Pattern) (guard : d1092 p = 1) : d496 p ≤ (0 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d496, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6170 p hg
    simpa only [d496, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d496, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6162 p hg
    simpa only [d496, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6206 (p : Pattern) (guard : d1092 p = 1) : d61 p ≤ (0 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5791 p hg
    simpa only [d1092, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare447 p hg
    simpa only [d1092, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6207 (p : Pattern) (guard : d1092 p = 1) : d473 p ≤ (0 : Int) + d43 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d473, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6206 p hg
    simpa only [d473, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d473, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6159 p hg
    simpa only [d473, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6208 (p : Pattern) (guard : d1092 p = 1) : d497 p ≤ (0 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d497, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6205 p hg
    simpa only [d497, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d497, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6207 p hg
    simpa only [d497, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6209 (p : Pattern) (guard : d1092 p = 1) : d498 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d498, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6161 p hg
    simpa only [d498, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d498, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6208 p hg
    simpa only [d498, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6210 (p : Pattern) (guard : d1093 p = 1) : d499 p ≤ (0 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5714 p hg
    simpa only [d1093, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6209 p hg
    simpa only [d1093, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6211 (p : Pattern) (guard : d0 p = 1) : d522 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6212 (p : Pattern) (guard : d1094 p = 1) : d523 p ≤ (0 : Int) + d208 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d523, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6210 p hg
    simpa only [d1094, d523, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d523, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6211 p hg
    simpa only [d1094, d523, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6213 (p : Pattern) (guard : d1092 p = 1) : d510 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6170 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6156 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6214 (p : Pattern) (guard : d1092 p = 1) : d470 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d470, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6156 p hg
    simpa only [d470, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d470, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6159 p hg
    simpa only [d470, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6215 (p : Pattern) (guard : d1092 p = 1) : d511 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d511, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6213 p hg
    simpa only [d511, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d511, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6214 p hg
    simpa only [d511, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6216 (p : Pattern) (guard : d1092 p = 1) : d491 p ≤ (0 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d491, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6214 p hg
    simpa only [d491, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d491, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1645 p hg
    simpa only [d491, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6217 (p : Pattern) (guard : d1092 p = 1) : d512 p ≤ (0 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d512, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6215 p hg
    simpa only [d512, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d512, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6216 p hg
    simpa only [d512, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6218 (p : Pattern) (guard : d1093 p = 1) : d513 p ≤ (0 : Int) + d77 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5771 p hg
    simpa only [d1093, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6217 p hg
    simpa only [d1093, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6219 (p : Pattern) (guard : d0 p = 1) : d526 p ≤ (0 : Int) + d164 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6220 (p : Pattern) (guard : d1094 p = 1) : d527 p ≤ (0 : Int) + d209 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d527, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6218 p hg
    simpa only [d1094, d527, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d527, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6219 p hg
    simpa only [d1094, d527, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6221 (p : Pattern) (guard : d1094 p = 1) : d528 p ≤ (0 : Int) + d210 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d528, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6212 p hg
    simpa only [d528, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1094 p = 1 := by simpa only [d528, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6220 p hg
    simpa only [d528, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6222 (p : Pattern) (guard : d1092 p = 1) : d58 p ≤ (0 : Int) + d211 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5877 p hg
    simpa only [d1092, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5169 p hg
    simpa only [d1092, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6223 (p : Pattern) (guard : d1092 p = 1) : d519 p ≤ (0 : Int) + d212 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d519, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6179 p hg
    simpa only [d519, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d519, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6222 p hg
    simpa only [d519, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6224 (p : Pattern) (guard : d1092 p = 1) : d520 p ≤ (0 : Int) + d213 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d520, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6223 p hg
    simpa only [d520, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d520, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6189 p hg
    simpa only [d520, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6225 (p : Pattern) (guard : d1092 p = 1) : d529 p ≤ (0 : Int) + d214 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d529, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6197 p hg
    simpa only [d529, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d529, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6224 p hg
    simpa only [d529, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6226 (p : Pattern) (guard : d1093 p = 1) : d530 p ≤ (0 : Int) + d215 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, d530, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5795 p hg
    simpa only [d1093, d530, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, d530, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6225 p hg
    simpa only [d1093, d530, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6227 (p : Pattern) (guard : d0 p = 1) : d531 p ≤ (0 : Int) + d164 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6228 (p : Pattern) (guard : d1094 p = 1) : d532 p ≤ (0 : Int) + d216 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d532, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6226 p hg
    simpa only [d1094, d532, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d532, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6227 p hg
    simpa only [d1094, d532, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6229 (p : Pattern) (guard : d1092 p = 1) : d52 p ≤ (0 : Int) + d217 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d1092, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5163 p hg
    simpa only [d1092, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6230 (p : Pattern) (guard : d1092 p = 1) : d54 p ≤ (0 : Int) + d218 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5698 p hg
    simpa only [d1092, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5165 p hg
    simpa only [d1092, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6231 (p : Pattern) (guard : d1092 p = 1) : d470 p ≤ (0 : Int) + d219 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d470, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6229 p hg
    simpa only [d470, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d470, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6230 p hg
    simpa only [d470, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6232 (p : Pattern) (guard : d1092 p = 1) : d524 p ≤ (0 : Int) + d220 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d524, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6229 p hg
    simpa only [d524, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d524, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6231 p hg
    simpa only [d524, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6233 (p : Pattern) (guard : d1092 p = 1) : d491 p ≤ (0 : Int) + d221 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d491, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6231 p hg
    simpa only [d491, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d491, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2080 p hg
    simpa only [d491, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6234 (p : Pattern) (guard : d1092 p = 1) : d525 p ≤ (0 : Int) + d222 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d525, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6232 p hg
    simpa only [d525, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d525, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6233 p hg
    simpa only [d525, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6235 (p : Pattern) (guard : d1093 p = 1) : d533 p ≤ (0 : Int) + d223 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1093, d533, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5806 p hg
    simpa only [d1093, d533, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1093, d533, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6234 p hg
    simpa only [d1093, d533, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6236 (p : Pattern) (guard : d1094 p = 1) : d534 p ≤ (0 : Int) + d224 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1093 p = 1 := by simpa only [d1094, d534, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6235 p hg
    simpa only [d1094, d534, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1094, d534, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2038 p hg
    simpa only [d1094, d534, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6237 (p : Pattern) (guard : d1094 p = 1) : d535 p ≤ (0 : Int) + d225 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d535, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6228 p hg
    simpa only [d535, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1094 p = 1 := by simpa only [d535, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6236 p hg
    simpa only [d535, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6238 (p : Pattern) (guard : d1094 p = 1) : d536 p ≤ (0 : Int) + d226 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d536, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6221 p hg
    simpa only [d536, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1094 p = 1 := by simpa only [d536, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6237 p hg
    simpa only [d536, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6239 (p : Pattern) (guard : d1094 p = 1) : d537 p ≤ (0 : Int) + d227 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d537, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6204 p hg
    simpa only [d537, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1094 p = 1 := by simpa only [d537, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6238 p hg
    simpa only [d537, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6240 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6241 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6242 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6243 (p : Pattern) (guard : d1167 p = 1) : d7 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6241 p hg
    simpa only [d1167, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6242 p hg
    simpa only [d1167, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6244 (p : Pattern) (guard : d1412 p = 1) : d8 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1412, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6240 p hg
    simpa only [d1412, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d1412, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6243 p hg
    simpa only [d1412, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6245 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6246 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (0 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare698 p hg
    simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6247 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6248 (p : Pattern) (guard : d1167 p = 1) : d13 p ≤ (0 : Int) + d11 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6246 p hg
    simpa only [d1167, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6247 p hg
    simpa only [d1167, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6249 (p : Pattern) (guard : d1412 p = 1) : d14 p ≤ (0 : Int) + d11 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1412, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6245 p hg
    simpa only [d1412, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d1412, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6248 p hg
    simpa only [d1412, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6250 (p : Pattern) (guard : d1412 p = 1) : d15 p ≤ (0 : Int) + d1413 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d15, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6244 p hg
    simpa only [d15, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d15, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6249 p hg
    simpa only [d15, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6251 (p : Pattern) (guard : d1412 p = 1) : d16 p ≤ (0 : Int) + d1414 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d16, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6244 p hg
    simpa only [d16, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d16, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6250 p hg
    simpa only [d16, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6252 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (0 : Int) + d17 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6253 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d17 p := by
  omega
theorem compare6254 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d17 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6255 (p : Pattern) (guard : d1167 p = 1) : d19 p ≤ (0 : Int) + d17 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6253 p hg
    simpa only [d1167, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6254 p hg
    simpa only [d1167, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6256 (p : Pattern) (guard : d1412 p = 1) : d20 p ≤ (0 : Int) + d17 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1412, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6252 p hg
    simpa only [d1412, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d1412, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6255 p hg
    simpa only [d1412, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6257 (p : Pattern) (guard : d0 p = 1) : d22 p ≤ (0 : Int) + d21 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6258 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d21 p := by
  omega
theorem compare6259 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d21 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6260 (p : Pattern) (guard : d1167 p = 1) : d23 p ≤ (0 : Int) + d21 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6258 p hg
    simpa only [d1167, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6259 p hg
    simpa only [d1167, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6261 (p : Pattern) (guard : d1412 p = 1) : d24 p ≤ (0 : Int) + d21 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1412, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6257 p hg
    simpa only [d1412, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d1412, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6260 p hg
    simpa only [d1412, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6262 (p : Pattern) (guard : d1412 p = 1) : d25 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d25, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6256 p hg
    simpa only [d25, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d25, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6261 p hg
    simpa only [d25, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6263 (p : Pattern) (guard : d1412 p = 1) : d26 p ≤ (0 : Int) + d1416 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d26, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6256 p hg
    simpa only [d26, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d26, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6262 p hg
    simpa only [d26, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6264 (p : Pattern) (guard : d1412 p = 1) : d27 p ≤ (0 : Int) + d1417 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d27, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6251 p hg
    simpa only [d27, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d27, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6263 p hg
    simpa only [d27, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6265 (p : Pattern) (guard : d1412 p = 1) : d28 p ≤ (0 : Int) + d1418 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d28, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6251 p hg
    simpa only [d28, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d28, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6264 p hg
    simpa only [d28, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6266 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (0 : Int) + d30 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6267 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d30 p := by
  omega
theorem compare6268 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d30 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6269 (p : Pattern) (guard : d1167 p = 1) : d32 p ≤ (0 : Int) + d30 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6267 p hg
    simpa only [d1167, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6268 p hg
    simpa only [d1167, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6270 (p : Pattern) (guard : d1412 p = 1) : d33 p ≤ (0 : Int) + d30 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1412, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6266 p hg
    simpa only [d1412, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d1412, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6269 p hg
    simpa only [d1412, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6271 (p : Pattern) (guard : d1412 p = 1) : d34 p ≤ (0 : Int) + d1419 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d34, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6270 p hg
    simpa only [d34, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d34, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6261 p hg
    simpa only [d34, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6272 (p : Pattern) (guard : d1412 p = 1) : d35 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d35, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6270 p hg
    simpa only [d35, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d35, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6271 p hg
    simpa only [d35, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6273 (p : Pattern) (guard : d1412 p = 1) : d36 p ≤ (0 : Int) + d1421 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d36, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6251 p hg
    simpa only [d36, d1421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d36, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6272 p hg
    simpa only [d36, d1421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6274 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d5 p := by
  omega
theorem compare6275 (p : Pattern) (guard : d1167 p = 1) : d37 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6274 p hg
    simpa only [d1167, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6242 p hg
    simpa only [d1167, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6276 (p : Pattern) (guard : d1412 p = 1) : d38 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1412, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6240 p hg
    simpa only [d1412, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d1412, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6275 p hg
    simpa only [d1412, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6277 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (0 : Int) + d11 p := by
  omega
theorem compare6278 (p : Pattern) (guard : d1167 p = 1) : d39 p ≤ (0 : Int) + d11 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6277 p hg
    simpa only [d1167, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6247 p hg
    simpa only [d1167, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6279 (p : Pattern) (guard : d1412 p = 1) : d40 p ≤ (0 : Int) + d11 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1412, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6245 p hg
    simpa only [d1412, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d1412, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6278 p hg
    simpa only [d1412, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6280 (p : Pattern) (guard : d1412 p = 1) : d41 p ≤ (0 : Int) + d1413 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d41, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6276 p hg
    simpa only [d41, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d41, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6279 p hg
    simpa only [d41, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6281 (p : Pattern) (guard : d1412 p = 1) : d42 p ≤ (0 : Int) + d1414 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d42, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6276 p hg
    simpa only [d42, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d42, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6280 p hg
    simpa only [d42, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6282 (p : Pattern) (guard : d1412 p = 1) : d43 p ≤ (0 : Int) + d1417 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d43, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6281 p hg
    simpa only [d43, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d43, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6263 p hg
    simpa only [d43, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6283 (p : Pattern) (guard : d1412 p = 1) : d44 p ≤ (0 : Int) + d1422 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d44, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6273 p hg
    simpa only [d44, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d44, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6282 p hg
    simpa only [d44, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6284 (p : Pattern) (guard : d1412 p = 1) : d45 p ≤ (0 : Int) + d1423 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d45, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6265 p hg
    simpa only [d45, d1423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d45, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6283 p hg
    simpa only [d45, d1423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6285 (p : Pattern) (guard : d1412 p = 1) : d46 p ≤ (0 : Int) + d1424 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d46, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6250 p hg
    simpa only [d46, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d46, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6262 p hg
    simpa only [d46, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6286 (p : Pattern) (guard : d1412 p = 1) : d47 p ≤ (0 : Int) + d1425 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d47, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6250 p hg
    simpa only [d47, d1425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d47, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6285 p hg
    simpa only [d47, d1425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6287 (p : Pattern) (guard : d1412 p = 1) : d48 p ≤ (0 : Int) + d1426 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d48, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6250 p hg
    simpa only [d48, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d48, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6271 p hg
    simpa only [d48, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6288 (p : Pattern) (guard : d1412 p = 1) : d49 p ≤ (0 : Int) + d1424 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d49, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6280 p hg
    simpa only [d49, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d49, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6262 p hg
    simpa only [d49, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6289 (p : Pattern) (guard : d1412 p = 1) : d50 p ≤ (0 : Int) + d1427 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d50, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6287 p hg
    simpa only [d50, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d50, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6288 p hg
    simpa only [d50, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6290 (p : Pattern) (guard : d1412 p = 1) : d51 p ≤ (0 : Int) + d1428 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d51, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6286 p hg
    simpa only [d51, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d51, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6289 p hg
    simpa only [d51, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6291 (p : Pattern) (guard : d1412 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare6292 (p : Pattern) (guard : d1412 p = 1) : d52 p ≤ (0 : Int) + d1429 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d52, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6244 p hg
    simpa only [d52, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d52, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6291 p hg
    simpa only [d52, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6293 (p : Pattern) (guard : d1412 p = 1) : d53 p ≤ (0 : Int) + d1430 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d53, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6250 p hg
    simpa only [d53, d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d53, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6292 p hg
    simpa only [d53, d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6294 (p : Pattern) (guard : d1412 p = 1) : d54 p ≤ (0 : Int) + d1431 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d54, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6256 p hg
    simpa only [d54, d1431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d54, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6291 p hg
    simpa only [d54, d1431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6295 (p : Pattern) (guard : d1412 p = 1) : d55 p ≤ (0 : Int) + d1432 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d55, d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6262 p hg
    simpa only [d55, d1432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d55, d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6294 p hg
    simpa only [d55, d1432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6296 (p : Pattern) (guard : d1412 p = 1) : d56 p ≤ (0 : Int) + d1433 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d56, d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6293 p hg
    simpa only [d56, d1433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d56, d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6295 p hg
    simpa only [d56, d1433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6297 (p : Pattern) (guard : d1412 p = 1) : d57 p ≤ (0 : Int) + d1434 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d57, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6293 p hg
    simpa only [d57, d1434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d57, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6296 p hg
    simpa only [d57, d1434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6298 (p : Pattern) (guard : d1412 p = 1) : d58 p ≤ (0 : Int) + d1435 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d58, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6270 p hg
    simpa only [d58, d1435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d58, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6291 p hg
    simpa only [d58, d1435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6299 (p : Pattern) (guard : d1412 p = 1) : d59 p ≤ (0 : Int) + d1436 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d59, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6271 p hg
    simpa only [d59, d1436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d59, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6298 p hg
    simpa only [d59, d1436, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
