/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons200
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare28140 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d3 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28139 p hg
    simpa only [d6558, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26447 p hg
    simpa only [d6558, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28141 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6748 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3374, d6748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28139 p hg
    simpa only [d6558, d3374, d6748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3374, d6748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23417 p hg
    simpa only [d6558, d3374, d6748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28142 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6749 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28140 p hg
    simpa only [d6749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28141 p hg
    simpa only [d6749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28143 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6750 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3374, d6750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28139 p hg
    simpa only [d6558, d3374, d6750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3374, d6750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26453 p hg
    simpa only [d6558, d3374, d6750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28144 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d3374 p := by
  omega
theorem compare28145 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6751 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28143 p hg
    simpa only [d6751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28144 p hg
    simpa only [d6751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28146 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6752 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28142 p hg
    simpa only [d6752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28145 p hg
    simpa only [d6752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28147 (p : Pattern) (guard : d6558 p = 1) : d3375 p ≤ (0 : Int) + d6753 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3375, d6753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28146 p hg
    simpa only [d3375, d6753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3375, d6753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3375, d6753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28148 (p : Pattern) (guard : d6558 p = 1) : d3376 p ≤ (0 : Int) + d6754 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3376, d6754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28138 p hg
    simpa only [d3376, d6754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3376, d6754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28147 p hg
    simpa only [d3376, d6754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28149 (p : Pattern) (guard : d5842 p = 1) : d7 p ≤ (0 : Int) + d7 p := by
  omega
theorem compare28150 (p : Pattern) (guard : d6558 p = 1) : d3377 p ≤ (0 : Int) + d7 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28149 p hg
    simpa only [d6558, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26453 p hg
    simpa only [d6558, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28151 (p : Pattern) (guard : d6558 p = 1) : d3377 p ≤ (0 : Int) + d3377 p := by
  omega
theorem compare28152 (p : Pattern) (guard : d6558 p = 1) : d3377 p ≤ (0 : Int) + d6755 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28150 p hg
    simpa only [d6755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28151 p hg
    simpa only [d6755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28153 (p : Pattern) (guard : d6558 p = 1) : d3377 p ≤ (0 : Int) + d6756 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3377, d6756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28149 p hg
    simpa only [d6558, d3377, d6756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3377, d6756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23451 p hg
    simpa only [d6558, d3377, d6756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28154 (p : Pattern) (guard : d6558 p = 1) : d3377 p ≤ (0 : Int) + d6757 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28153 p hg
    simpa only [d6757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28151 p hg
    simpa only [d6757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28155 (p : Pattern) (guard : d6558 p = 1) : d3377 p ≤ (0 : Int) + d6758 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28152 p hg
    simpa only [d6758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28154 p hg
    simpa only [d6758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28156 (p : Pattern) (guard : d6558 p = 1) : d3378 p ≤ (0 : Int) + d6759 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3378, d6759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28155 p hg
    simpa only [d3378, d6759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3378, d6759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3378, d6759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28157 (p : Pattern) (guard : d6558 p = 1) : d3379 p ≤ (0 : Int) + d6760 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3379, d6760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28138 p hg
    simpa only [d3379, d6760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3379, d6760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28156 p hg
    simpa only [d3379, d6760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28158 (p : Pattern) (guard : d6558 p = 1) : d3380 p ≤ (0 : Int) + d6761 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3380, d6761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28148 p hg
    simpa only [d3380, d6761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3380, d6761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28157 p hg
    simpa only [d3380, d6761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28159 (p : Pattern) (guard : d6558 p = 1) : d3381 p ≤ (0 : Int) + d6762 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3381, d6762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28138 p hg
    simpa only [d3381, d6762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3381, d6762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3381, d6762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28160 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d6763 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3366, d6763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28117 p hg
    simpa only [d6558, d3366, d6763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3366, d6763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23451 p hg
    simpa only [d6558, d3366, d6763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28161 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d6764 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28118 p hg
    simpa only [d6764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28160 p hg
    simpa only [d6764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28162 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d3366 p := by
  omega
theorem compare28163 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d6765 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28119 p hg
    simpa only [d6765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28162 p hg
    simpa only [d6765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28164 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d6766 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28161 p hg
    simpa only [d6766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28163 p hg
    simpa only [d6766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28165 (p : Pattern) (guard : d6558 p = 1) : d3366 p ≤ (0 : Int) + d6767 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28118 p hg
    simpa only [d6767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28164 p hg
    simpa only [d6767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28166 (p : Pattern) (guard : d6558 p = 1) : d3382 p ≤ (0 : Int) + d6768 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3382, d6768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28165 p hg
    simpa only [d3382, d6768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3382, d6768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3382, d6768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28167 (p : Pattern) (guard : d6558 p = 1) : d3383 p ≤ (0 : Int) + d6769 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3383, d6769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28159 p hg
    simpa only [d3383, d6769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3383, d6769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28166 p hg
    simpa only [d3383, d6769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28168 (p : Pattern) (guard : d6558 p = 1) : d3384 p ≤ (0 : Int) + d6770 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3384, d6770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28158 p hg
    simpa only [d3384, d6770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3384, d6770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28167 p hg
    simpa only [d3384, d6770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28169 (p : Pattern) (guard : d6558 p = 1) : d3385 p ≤ (0 : Int) + d6771 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3385, d6771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28002 p hg
    simpa only [d3385, d6771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3385, d6771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3385, d6771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28170 (p : Pattern) (guard : d6558 p = 1) : d3386 p ≤ (0 : Int) + d6772 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3386, d6772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28167 p hg
    simpa only [d3386, d6772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3386, d6772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28169 p hg
    simpa only [d3386, d6772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28171 (p : Pattern) (guard : d6558 p = 1) : d3387 p ≤ (0 : Int) + d6773 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3387, d6773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28168 p hg
    simpa only [d3387, d6773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3387, d6773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28170 p hg
    simpa only [d3387, d6773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28172 (p : Pattern) (guard : d6558 p = 1) : d3388 p ≤ (0 : Int) + d6774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3388, d6774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28132 p hg
    simpa only [d3388, d6774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3388, d6774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28171 p hg
    simpa only [d3388, d6774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28173 (p : Pattern) (guard : d0 p = 1) : d39 p ≤ (0 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28174 (p : Pattern) (guard : d6558 p = 1) : d3389 p ≤ (0 : Int) + d1 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28099 p hg
    simpa only [d6558, d3389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28173 p hg
    simpa only [d6558, d3389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28175 (p : Pattern) (guard : d6558 p = 1) : d3390 p ≤ (0 : Int) + d1 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28174 p hg
    simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28102 p hg
    simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28176 (p : Pattern) (guard : d6558 p = 1) : d3391 p ≤ (0 : Int) + d1 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28175 p hg
    simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28102 p hg
    simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28177 (p : Pattern) (guard : d6558 p = 1) : d3392 p ≤ (0 : Int) + d6722 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3392, d6722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28176 p hg
    simpa only [d3392, d6722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3392, d6722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28107 p hg
    simpa only [d3392, d6722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28178 (p : Pattern) (guard : d6558 p = 1) : d3393 p ≤ (0 : Int) + d6727 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3393, d6727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28177 p hg
    simpa only [d3393, d6727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3393, d6727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28112 p hg
    simpa only [d3393, d6727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28179 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6775 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28140 p hg
    simpa only [d6775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28143 p hg
    simpa only [d6775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28180 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6776 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28179 p hg
    simpa only [d6776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28143 p hg
    simpa only [d6776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28181 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6777 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28140 p hg
    simpa only [d6777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28180 p hg
    simpa only [d6777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28182 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6778 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3374, d6778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28139 p hg
    simpa only [d6558, d3374, d6778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3374, d6778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26436 p hg
    simpa only [d6558, d3374, d6778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28183 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6779 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28140 p hg
    simpa only [d6779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28182 p hg
    simpa only [d6779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28184 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6780 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28183 p hg
    simpa only [d6780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28182 p hg
    simpa only [d6780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28185 (p : Pattern) (guard : d6558 p = 1) : d3375 p ≤ (0 : Int) + d6781 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3375, d6781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28184 p hg
    simpa only [d3375, d6781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3375, d6781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3375, d6781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28186 (p : Pattern) (guard : d6558 p = 1) : d3394 p ≤ (0 : Int) + d6782 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3394, d6782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28181 p hg
    simpa only [d3394, d6782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3394, d6782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28185 p hg
    simpa only [d3394, d6782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28187 (p : Pattern) (guard : d6558 p = 1) : d3395 p ≤ (0 : Int) + d6783 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3395, d6783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28178 p hg
    simpa only [d3395, d6783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3395, d6783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28186 p hg
    simpa only [d3395, d6783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28188 (p : Pattern) (guard : d6558 p = 1) : d3396 p ≤ (0 : Int) + d6784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3396, d6784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28127 p hg
    simpa only [d3396, d6784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3396, d6784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27990 p hg
    simpa only [d3396, d6784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28189 (p : Pattern) (guard : d6558 p = 1) : d3397 p ≤ (0 : Int) + d6785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3397, d6785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28187 p hg
    simpa only [d3397, d6785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3397, d6785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28188 p hg
    simpa only [d3397, d6785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28190 (p : Pattern) (guard : d6558 p = 1) : d3398 p ≤ (0 : Int) + d6786 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3398, d6786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28127 p hg
    simpa only [d3398, d6786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3398, d6786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27993 p hg
    simpa only [d3398, d6786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28191 (p : Pattern) (guard : d6558 p = 1) : d3399 p ≤ (0 : Int) + d6787 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3399, d6787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28190 p hg
    simpa only [d3399, d6787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3399, d6787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3399, d6787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28192 (p : Pattern) (guard : d6558 p = 1) : d3400 p ≤ (0 : Int) + d6788 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3400, d6788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28189 p hg
    simpa only [d3400, d6788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3400, d6788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28191 p hg
    simpa only [d3400, d6788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28193 (p : Pattern) (guard : d6558 p = 1) : d3374 p ≤ (0 : Int) + d6789 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28140 p hg
    simpa only [d6789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28146 p hg
    simpa only [d6789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28194 (p : Pattern) (guard : d6558 p = 1) : d3401 p ≤ (0 : Int) + d6790 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3401, d6790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28193 p hg
    simpa only [d3401, d6790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3401, d6790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3401, d6790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28195 (p : Pattern) (guard : d6558 p = 1) : d3402 p ≤ (0 : Int) + d6791 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3402, d6791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28157 p hg
    simpa only [d3402, d6791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3402, d6791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28194 p hg
    simpa only [d3402, d6791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28196 (p : Pattern) (guard : d6558 p = 1) : d3403 p ≤ (0 : Int) + d6792 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3403, d6792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28166 p hg
    simpa only [d3403, d6792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3403, d6792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28002 p hg
    simpa only [d3403, d6792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28197 (p : Pattern) (guard : d6558 p = 1) : d3404 p ≤ (0 : Int) + d6793 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3404, d6793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28195 p hg
    simpa only [d3404, d6793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3404, d6793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28196 p hg
    simpa only [d3404, d6793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28198 (p : Pattern) (guard : d6558 p = 1) : d3405 p ≤ (0 : Int) + d6794 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3405, d6794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28166 p hg
    simpa only [d3405, d6794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3405, d6794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28004 p hg
    simpa only [d3405, d6794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28199 (p : Pattern) (guard : d6558 p = 1) : d3406 p ≤ (0 : Int) + d6795 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3406, d6795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28198 p hg
    simpa only [d3406, d6795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3406, d6795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3406, d6795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28200 (p : Pattern) (guard : d6558 p = 1) : d3407 p ≤ (0 : Int) + d6796 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3407, d6796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28197 p hg
    simpa only [d3407, d6796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3407, d6796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28199 p hg
    simpa only [d3407, d6796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28201 (p : Pattern) (guard : d6558 p = 1) : d3408 p ≤ (0 : Int) + d6797 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3408, d6797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28192 p hg
    simpa only [d3408, d6797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3408, d6797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28200 p hg
    simpa only [d3408, d6797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28202 (p : Pattern) (guard : d6558 p = 1) : d3409 p ≤ (0 : Int) + d6798 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3409, d6798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28172 p hg
    simpa only [d3409, d6798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3409, d6798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28201 p hg
    simpa only [d3409, d6798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28203 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6799 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28105 p hg
    simpa only [d6799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28133 p hg
    simpa only [d6799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28204 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6800 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28134 p hg
    simpa only [d6800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28203 p hg
    simpa only [d6800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28205 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6801 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28102 p hg
    simpa only [d6801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28204 p hg
    simpa only [d6801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28206 (p : Pattern) (guard : d6558 p = 1) : d3362 p ≤ (0 : Int) + d6802 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3362, d6802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28107 p hg
    simpa only [d3362, d6802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3362, d6802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3362, d6802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28207 (p : Pattern) (guard : d6558 p = 1) : d3364 p ≤ (0 : Int) + d6803 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3364, d6803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28205 p hg
    simpa only [d3364, d6803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3364, d6803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28206 p hg
    simpa only [d3364, d6803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28208 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6804 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3358, d6804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28099 p hg
    simpa only [d6558, d3358, d6804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3358, d6804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23417 p hg
    simpa only [d6558, d3358, d6804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28209 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6805 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28105 p hg
    simpa only [d6805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28208 p hg
    simpa only [d6805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28210 (p : Pattern) (guard : d6558 p = 1) : d3358 p ≤ (0 : Int) + d6806 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28134 p hg
    simpa only [d6806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28209 p hg
    simpa only [d6806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28211 (p : Pattern) (guard : d6558 p = 1) : d3362 p ≤ (0 : Int) + d6807 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3362, d6807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28210 p hg
    simpa only [d3362, d6807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3362, d6807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3362, d6807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28212 (p : Pattern) (guard : d6558 p = 1) : d3364 p ≤ (0 : Int) + d6808 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3364, d6808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28138 p hg
    simpa only [d3364, d6808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3364, d6808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28211 p hg
    simpa only [d3364, d6808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28213 (p : Pattern) (guard : d6558 p = 1) : d3364 p ≤ (0 : Int) + d6809 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28207 p hg
    simpa only [d6809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28212 p hg
    simpa only [d6809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28214 (p : Pattern) (guard : d6558 p = 1) : d3362 p ≤ (0 : Int) + d6810 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3362, d6810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28137 p hg
    simpa only [d3362, d6810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3362, d6810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3362, d6810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28215 (p : Pattern) (guard : d6558 p = 1) : d3364 p ≤ (0 : Int) + d6811 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3364, d6811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28138 p hg
    simpa only [d3364, d6811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3364, d6811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28214 p hg
    simpa only [d3364, d6811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28216 (p : Pattern) (guard : d6558 p = 1) : d3367 p ≤ (0 : Int) + d6812 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3367, d6812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28164 p hg
    simpa only [d3367, d6812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3367, d6812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3367, d6812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28217 (p : Pattern) (guard : d6558 p = 1) : d3368 p ≤ (0 : Int) + d6813 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3368, d6813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28165 p hg
    simpa only [d3368, d6813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3368, d6813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28216 p hg
    simpa only [d3368, d6813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28218 (p : Pattern) (guard : d6558 p = 1) : d3369 p ≤ (0 : Int) + d6814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3369, d6814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28215 p hg
    simpa only [d3369, d6814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3369, d6814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28217 p hg
    simpa only [d3369, d6814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28219 (p : Pattern) (guard : d6558 p = 1) : d3410 p ≤ (0 : Int) + d6815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3410, d6815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28213 p hg
    simpa only [d3410, d6815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3410, d6815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28218 p hg
    simpa only [d3410, d6815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28220 (p : Pattern) (guard : d6558 p = 1) : d3372 p ≤ (0 : Int) + d6816 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3372, d6816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28218 p hg
    simpa only [d3372, d6816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3372, d6816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28130 p hg
    simpa only [d3372, d6816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28221 (p : Pattern) (guard : d6558 p = 1) : d3411 p ≤ (0 : Int) + d6817 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3411, d6817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28219 p hg
    simpa only [d3411, d6817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3411, d6817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28220 p hg
    simpa only [d3411, d6817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28222 (p : Pattern) (guard : d6558 p = 1) : d3394 p ≤ (0 : Int) + d6818 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3394, d6818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28193 p hg
    simpa only [d3394, d6818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3394, d6818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28147 p hg
    simpa only [d3394, d6818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28223 (p : Pattern) (guard : d6558 p = 1) : d3377 p ≤ (0 : Int) + d6819 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28150 p hg
    simpa only [d6819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28155 p hg
    simpa only [d6819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28224 (p : Pattern) (guard : d6558 p = 1) : d3412 p ≤ (0 : Int) + d6820 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3412, d6820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28223 p hg
    simpa only [d3412, d6820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3412, d6820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28156 p hg
    simpa only [d3412, d6820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28225 (p : Pattern) (guard : d6558 p = 1) : d3413 p ≤ (0 : Int) + d6821 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3413, d6821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28222 p hg
    simpa only [d3413, d6821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3413, d6821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28224 p hg
    simpa only [d3413, d6821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28226 (p : Pattern) (guard : d6558 p = 1) : d3414 p ≤ (0 : Int) + d6822 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3414, d6822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28225 p hg
    simpa only [d3414, d6822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3414, d6822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3414, d6822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28227 (p : Pattern) (guard : d6558 p = 1) : d3415 p ≤ (0 : Int) + d6823 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3415, d6823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28226 p hg
    simpa only [d3415, d6823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3415, d6823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3415, d6823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28228 (p : Pattern) (guard : d6558 p = 1) : d3416 p ≤ (0 : Int) + d6824 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3416, d6824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28221 p hg
    simpa only [d3416, d6824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3416, d6824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28227 p hg
    simpa only [d3416, d6824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28229 (p : Pattern) (guard : d6558 p = 1) : d3417 p ≤ (0 : Int) + d6825 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3417, d6825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28212 p hg
    simpa only [d3417, d6825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3417, d6825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28222 p hg
    simpa only [d3417, d6825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28230 (p : Pattern) (guard : d6558 p = 1) : d3396 p ≤ (0 : Int) + d6826 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3396, d6826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28217 p hg
    simpa only [d3396, d6826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3396, d6826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27990 p hg
    simpa only [d3396, d6826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28231 (p : Pattern) (guard : d6558 p = 1) : d3418 p ≤ (0 : Int) + d6827 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3418, d6827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28229 p hg
    simpa only [d3418, d6827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3418, d6827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28230 p hg
    simpa only [d3418, d6827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28232 (p : Pattern) (guard : d6558 p = 1) : d3398 p ≤ (0 : Int) + d6828 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3398, d6828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28217 p hg
    simpa only [d3398, d6828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3398, d6828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27993 p hg
    simpa only [d3398, d6828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28233 (p : Pattern) (guard : d6558 p = 1) : d3399 p ≤ (0 : Int) + d6829 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3399, d6829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28232 p hg
    simpa only [d3399, d6829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3399, d6829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3399, d6829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28234 (p : Pattern) (guard : d6558 p = 1) : d3419 p ≤ (0 : Int) + d6830 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3419, d6830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28231 p hg
    simpa only [d3419, d6830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3419, d6830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28233 p hg
    simpa only [d3419, d6830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28235 (p : Pattern) (guard : d6558 p = 1) : d3420 p ≤ (0 : Int) + d6831 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3420, d6831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28224 p hg
    simpa only [d3420, d6831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3420, d6831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3420, d6831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28236 (p : Pattern) (guard : d6558 p = 1) : d3421 p ≤ (0 : Int) + d6832 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3421, d6832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28235 p hg
    simpa only [d3421, d6832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3421, d6832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3421, d6832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28237 (p : Pattern) (guard : d6558 p = 1) : d3422 p ≤ (0 : Int) + d6833 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3422, d6833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28236 p hg
    simpa only [d3422, d6833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3422, d6833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3422, d6833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28238 (p : Pattern) (guard : d6558 p = 1) : d3423 p ≤ (0 : Int) + d6834 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3423, d6834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28234 p hg
    simpa only [d3423, d6834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3423, d6834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28237 p hg
    simpa only [d3423, d6834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28239 (p : Pattern) (guard : d6558 p = 1) : d3424 p ≤ (0 : Int) + d6835 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3424, d6835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28228 p hg
    simpa only [d3424, d6835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3424, d6835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28238 p hg
    simpa only [d3424, d6835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28240 (p : Pattern) (guard : d6558 p = 1) : d3425 p ≤ (0 : Int) + d6836 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3425, d6836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28202 p hg
    simpa only [d3425, d6836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3425, d6836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28239 p hg
    simpa only [d3425, d6836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28241 (p : Pattern) (guard : d6558 p = 1) : d3426 p ≤ (0 : Int) + d6837 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3426, d6837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28130 p hg
    simpa only [d3426, d6837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3426, d6837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3426, d6837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28242 (p : Pattern) (guard : d6558 p = 1) : d3427 p ≤ (0 : Int) + d6838 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3427, d6838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28241 p hg
    simpa only [d3427, d6838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3427, d6838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3427, d6838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28243 (p : Pattern) (guard : d6558 p = 1) : d3428 p ≤ (0 : Int) + d6839 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3428, d6839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28242 p hg
    simpa only [d3428, d6839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3428, d6839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3428, d6839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28244 (p : Pattern) (guard : d6558 p = 1) : d3429 p ≤ (0 : Int) + d6840 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3429, d6840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28243 p hg
    simpa only [d3429, d6840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3429, d6840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3429, d6840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28245 (p : Pattern) (guard : d6558 p = 1) : d3430 p ≤ (0 : Int) + d6841 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3430, d6841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28239 p hg
    simpa only [d3430, d6841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3430, d6841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28244 p hg
    simpa only [d3430, d6841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28246 (p : Pattern) (guard : d6558 p = 1) : d3431 p ≤ (0 : Int) + d6842 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3431, d6842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28240 p hg
    simpa only [d3431, d6842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3431, d6842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28245 p hg
    simpa only [d3431, d6842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28247 (p : Pattern) (guard : d6558 p = 1) : d3410 p ≤ (0 : Int) + d6738 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3410, d6738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28115 p hg
    simpa only [d3410, d6738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3410, d6738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28128 p hg
    simpa only [d3410, d6738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28248 (p : Pattern) (guard : d6558 p = 1) : d3411 p ≤ (0 : Int) + d6741 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3411, d6741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28247 p hg
    simpa only [d3411, d6741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3411, d6741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28131 p hg
    simpa only [d3411, d6741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28249 (p : Pattern) (guard : d6558 p = 1) : d3432 p ≤ (0 : Int) + d6774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3432, d6774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28248 p hg
    simpa only [d3432, d6774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3432, d6774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28171 p hg
    simpa only [d3432, d6774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28250 (p : Pattern) (guard : d6558 p = 1) : d3417 p ≤ (0 : Int) + d6783 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3417, d6783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28115 p hg
    simpa only [d3417, d6783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3417, d6783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28186 p hg
    simpa only [d3417, d6783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28251 (p : Pattern) (guard : d6558 p = 1) : d3418 p ≤ (0 : Int) + d6785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3418, d6785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28250 p hg
    simpa only [d3418, d6785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3418, d6785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28188 p hg
    simpa only [d3418, d6785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28252 (p : Pattern) (guard : d6558 p = 1) : d3419 p ≤ (0 : Int) + d6788 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3419, d6788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28251 p hg
    simpa only [d3419, d6788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3419, d6788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28191 p hg
    simpa only [d3419, d6788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28253 (p : Pattern) (guard : d6558 p = 1) : d3433 p ≤ (0 : Int) + d6797 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3433, d6797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28252 p hg
    simpa only [d3433, d6797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3433, d6797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28200 p hg
    simpa only [d3433, d6797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28254 (p : Pattern) (guard : d6558 p = 1) : d3434 p ≤ (0 : Int) + d6798 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3434, d6798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28249 p hg
    simpa only [d3434, d6798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3434, d6798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28253 p hg
    simpa only [d3434, d6798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28255 (p : Pattern) (guard : d6558 p = 1) : d3435 p ≤ (0 : Int) + d6836 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3435, d6836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28254 p hg
    simpa only [d3435, d6836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3435, d6836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28239 p hg
    simpa only [d3435, d6836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28256 (p : Pattern) (guard : d6558 p = 1) : d3436 p ≤ (0 : Int) + d6843 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3436, d6843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28239 p hg
    simpa only [d3436, d6843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3436, d6843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3436, d6843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28257 (p : Pattern) (guard : d6558 p = 1) : d3437 p ≤ (0 : Int) + d6844 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3437, d6844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28255 p hg
    simpa only [d3437, d6844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3437, d6844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28256 p hg
    simpa only [d3437, d6844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28258 (p : Pattern) (guard : d6558 p = 1) : d3438 p ≤ (0 : Int) + d6845 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3438, d6845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28246 p hg
    simpa only [d3438, d6845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3438, d6845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28257 p hg
    simpa only [d3438, d6845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28259 (p : Pattern) (guard : d6558 p = 1) : d3439 p ≤ (0 : Int) + d6846 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3439, d6846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28073 p hg
    simpa only [d3439, d6846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3439, d6846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28258 p hg
    simpa only [d3439, d6846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28260 (p : Pattern) (guard : d6558 p = 1) : d3440 p ≤ (0 : Int) + d6847 p := by
  cases selected : p 49 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3440, d6847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28098 p hg
    simpa only [d3440, d6847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3440, d6847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28259 p hg
    simpa only [d3440, d6847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28261 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d6848 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27892 p hg
    simpa only [d6848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27950 p hg
    simpa only [d6848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28262 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d6849 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27951 p hg
    simpa only [d6849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28261 p hg
    simpa only [d6849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28263 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d6850 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27891 p hg
    simpa only [d6850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28262 p hg
    simpa only [d6850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28264 (p : Pattern) (guard : d6558 p = 1) : d3240 p ≤ (0 : Int) + d6851 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3240, d6851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27894 p hg
    simpa only [d3240, d6851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3240, d6851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3240, d6851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28265 (p : Pattern) (guard : d6558 p = 1) : d3241 p ≤ (0 : Int) + d6852 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3241, d6852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28263 p hg
    simpa only [d3241, d6852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3241, d6852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28264 p hg
    simpa only [d3241, d6852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28266 (p : Pattern) (guard : d6558 p = 1) : d3242 p ≤ (0 : Int) + d6853 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3242, d6853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28014 p hg
    simpa only [d3242, d6853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3242, d6853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28265 p hg
    simpa only [d3242, d6853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28267 (p : Pattern) (guard : d6558 p = 1) : d3299 p ≤ (0 : Int) + d6854 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3299, d6854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28014 p hg
    simpa only [d3299, d6854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3299, d6854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28266 p hg
    simpa only [d3299, d6854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28268 (p : Pattern) (guard : d6558 p = 1) : d3248 p ≤ (0 : Int) + d6855 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3248, d6855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28266 p hg
    simpa only [d3248, d6855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3248, d6855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28029 p hg
    simpa only [d3248, d6855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28269 (p : Pattern) (guard : d6558 p = 1) : d3300 p ≤ (0 : Int) + d6856 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3300, d6856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28267 p hg
    simpa only [d3300, d6856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3300, d6856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28268 p hg
    simpa only [d3300, d6856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28270 (p : Pattern) (guard : d6558 p = 1) : d3441 p ≤ (0 : Int) + d6857 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3441, d6857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27997 p hg
    simpa only [d3441, d6857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3441, d6857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27940 p hg
    simpa only [d3441, d6857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28271 (p : Pattern) (guard : d6558 p = 1) : d3442 p ≤ (0 : Int) + d6858 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3442, d6858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28032 p hg
    simpa only [d3442, d6858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3442, d6858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28270 p hg
    simpa only [d3442, d6858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28272 (p : Pattern) (guard : d6558 p = 1) : d3443 p ≤ (0 : Int) + d6859 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3443, d6859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27997 p hg
    simpa only [d3443, d6859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3443, d6859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27948 p hg
    simpa only [d3443, d6859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28273 (p : Pattern) (guard : d6558 p = 1) : d3444 p ≤ (0 : Int) + d6860 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3444, d6860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28033 p hg
    simpa only [d3444, d6860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3444, d6860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3444, d6860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28274 (p : Pattern) (guard : d6558 p = 1) : d3445 p ≤ (0 : Int) + d6861 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3445, d6861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28272 p hg
    simpa only [d3445, d6861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3445, d6861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28273 p hg
    simpa only [d3445, d6861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28275 (p : Pattern) (guard : d6558 p = 1) : d3446 p ≤ (0 : Int) + d6862 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3446, d6862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28271 p hg
    simpa only [d3446, d6862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3446, d6862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28274 p hg
    simpa only [d3446, d6862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28276 (p : Pattern) (guard : d6558 p = 1) : d3447 p ≤ (0 : Int) + d6863 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3447, d6863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27998 p hg
    simpa only [d3447, d6863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3447, d6863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28273 p hg
    simpa only [d3447, d6863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28277 (p : Pattern) (guard : d6558 p = 1) : d3448 p ≤ (0 : Int) + d6864 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3448, d6864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28276 p hg
    simpa only [d3448, d6864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3448, d6864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28005 p hg
    simpa only [d3448, d6864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28278 (p : Pattern) (guard : d6558 p = 1) : d3449 p ≤ (0 : Int) + d6865 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3449, d6865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28275 p hg
    simpa only [d3449, d6865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3449, d6865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28277 p hg
    simpa only [d3449, d6865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28279 (p : Pattern) (guard : d6558 p = 1) : d3450 p ≤ (0 : Int) + d6866 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3450, d6866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28269 p hg
    simpa only [d3450, d6866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3450, d6866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28278 p hg
    simpa only [d3450, d6866, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
