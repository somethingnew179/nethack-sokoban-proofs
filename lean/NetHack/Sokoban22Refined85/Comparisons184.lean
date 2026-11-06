/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons183
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare25760 (p : Pattern) (guard : d5540 p = 1) : d3172 p ≤ (2 : Int) + d6289 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3172, d6289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25759 p hg
    simpa only [d3172, d6289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3172, d6289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3172, d6289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25761 (p : Pattern) (guard : d5540 p = 1) : d3173 p ≤ (2 : Int) + d6290 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3173, d6290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25757 p hg
    simpa only [d3173, d6290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3173, d6290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25760 p hg
    simpa only [d3173, d6290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25762 (p : Pattern) (guard : d5540 p = 1) : d3174 p ≤ (2 : Int) + d6291 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3174, d6291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25754 p hg
    simpa only [d3174, d6291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3174, d6291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25761 p hg
    simpa only [d3174, d6291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25763 (p : Pattern) (guard : d0 p = 1) : d3175 p ≤ (2 : Int) + d1895 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25764 (p : Pattern) (guard : d5540 p = 1) : d3176 p ≤ (2 : Int) + d1895 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d3176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25545 p hg
    simpa only [d5540, d3176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d3176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25763 p hg
    simpa only [d5540, d3176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25765 (p : Pattern) (guard : d5540 p = 1) : d3177 p ≤ (2 : Int) + d6169 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3177, d6169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25571 p hg
    simpa only [d3177, d6169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3177, d6169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25764 p hg
    simpa only [d3177, d6169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25766 (p : Pattern) (guard : d5540 p = 1) : d2126 p ≤ (2 : Int) + d6156 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2126, d6156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25574 p hg
    simpa only [d2126, d6156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2126, d6156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2126, d6156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25767 (p : Pattern) (guard : d5540 p = 1) : d3178 p ≤ (2 : Int) + d6195 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3178, d6195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25765 p hg
    simpa only [d3178, d6195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3178, d6195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25766 p hg
    simpa only [d3178, d6195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25768 (p : Pattern) (guard : d5540 p = 1) : d3179 p ≤ (2 : Int) + d6202 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3179, d6202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25749 p hg
    simpa only [d3179, d6202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3179, d6202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25767 p hg
    simpa only [d3179, d6202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25769 (p : Pattern) (guard : d0 p = 1) : d2135 p ≤ (2 : Int) + d1964 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25770 (p : Pattern) (guard : d5540 p = 1) : d2136 p ≤ (2 : Int) + d1964 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25560 p hg
    simpa only [d5540, d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25769 p hg
    simpa only [d5540, d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25771 (p : Pattern) (guard : d5540 p = 1) : d3180 p ≤ (2 : Int) + d6148 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3180, d6148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25522 p hg
    simpa only [d3180, d6148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3180, d6148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25770 p hg
    simpa only [d3180, d6148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25772 (p : Pattern) (guard : d5540 p = 1) : d2131 p ≤ (2 : Int) + d6189 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2131, d6189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25526 p hg
    simpa only [d2131, d6189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2131, d6189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2131, d6189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25773 (p : Pattern) (guard : d5540 p = 1) : d3181 p ≤ (2 : Int) + d6190 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3181, d6190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25771 p hg
    simpa only [d3181, d6190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3181, d6190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25772 p hg
    simpa only [d3181, d6190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25774 (p : Pattern) (guard : d5540 p = 1) : d3182 p ≤ (2 : Int) + d6275 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3182, d6275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25773 p hg
    simpa only [d3182, d6275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3182, d6275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3182, d6275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25775 (p : Pattern) (guard : d5540 p = 1) : d3183 p ≤ (2 : Int) + d6276 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3183, d6276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25768 p hg
    simpa only [d3183, d6276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3183, d6276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25774 p hg
    simpa only [d3183, d6276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25776 (p : Pattern) (guard : d5540 p = 1) : d2137 p ≤ (2 : Int) + d6189 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2137, d6189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25770 p hg
    simpa only [d2137, d6189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2137, d6189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2137, d6189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25777 (p : Pattern) (guard : d5540 p = 1) : d3184 p ≤ (2 : Int) + d6190 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3184, d6190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25563 p hg
    simpa only [d3184, d6190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3184, d6190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25776 p hg
    simpa only [d3184, d6190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25778 (p : Pattern) (guard : d5540 p = 1) : d3185 p ≤ (2 : Int) + d6275 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3185, d6275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25777 p hg
    simpa only [d3185, d6275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3185, d6275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3185, d6275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25779 (p : Pattern) (guard : d5540 p = 1) : d3186 p ≤ (2 : Int) + d6277 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3186, d6277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25778 p hg
    simpa only [d3186, d6277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3186, d6277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3186, d6277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25780 (p : Pattern) (guard : d5540 p = 1) : d3187 p ≤ (2 : Int) + d6278 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3187, d6278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25775 p hg
    simpa only [d3187, d6278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3187, d6278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25779 p hg
    simpa only [d3187, d6278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25781 (p : Pattern) (guard : d5540 p = 1) : d3188 p ≤ (2 : Int) + d6292 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3188, d6292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25563 p hg
    simpa only [d3188, d6292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3188, d6292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25556 p hg
    simpa only [d3188, d6292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25782 (p : Pattern) (guard : d5540 p = 1) : d3189 p ≤ (2 : Int) + d6293 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3189, d6293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25781 p hg
    simpa only [d3189, d6293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3189, d6293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25564 p hg
    simpa only [d3189, d6293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25783 (p : Pattern) (guard : d5540 p = 1) : d3190 p ≤ (2 : Int) + d6294 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3190, d6294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25782 p hg
    simpa only [d3190, d6294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3190, d6294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25759 p hg
    simpa only [d3190, d6294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25784 (p : Pattern) (guard : d5540 p = 1) : d3191 p ≤ (2 : Int) + d6295 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3191, d6295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25404 p hg
    simpa only [d3191, d6295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3191, d6295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3191, d6295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25785 (p : Pattern) (guard : d5540 p = 1) : d3192 p ≤ (2 : Int) + d6296 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3192, d6296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25783 p hg
    simpa only [d3192, d6296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3192, d6296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25784 p hg
    simpa only [d3192, d6296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25786 (p : Pattern) (guard : d5540 p = 1) : d3193 p ≤ (2 : Int) + d6297 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3193, d6297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25780 p hg
    simpa only [d3193, d6297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3193, d6297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25785 p hg
    simpa only [d3193, d6297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25787 (p : Pattern) (guard : d5540 p = 1) : d3194 p ≤ (2 : Int) + d6298 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3194, d6298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25762 p hg
    simpa only [d3194, d6298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3194, d6298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25786 p hg
    simpa only [d3194, d6298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25788 (p : Pattern) (guard : d5540 p = 1) : d3195 p ≤ (2 : Int) + d6188 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25610 p hg
    simpa only [d3195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25613 p hg
    simpa only [d3195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25789 (p : Pattern) (guard : d5540 p = 1) : d3196 p ≤ (2 : Int) + d6299 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3196, d6299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25620 p hg
    simpa only [d3196, d6299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3196, d6299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25435 p hg
    simpa only [d3196, d6299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25790 (p : Pattern) (guard : d5540 p = 1) : d3197 p ≤ (2 : Int) + d6300 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3197, d6300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25788 p hg
    simpa only [d3197, d6300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3197, d6300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25789 p hg
    simpa only [d3197, d6300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25791 (p : Pattern) (guard : d5540 p = 1) : d3198 p ≤ (2 : Int) + d6301 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3198, d6301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25790 p hg
    simpa only [d3198, d6301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3198, d6301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25632 p hg
    simpa only [d3198, d6301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25792 (p : Pattern) (guard : d5540 p = 1) : d3199 p ≤ (2 : Int) + d6302 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3199, d6302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25791 p hg
    simpa only [d3199, d6302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3199, d6302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25636 p hg
    simpa only [d3199, d6302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25793 (p : Pattern) (guard : d0 p = 1) : d2156 p ≤ (2 : Int) + d1895 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25794 (p : Pattern) (guard : d5540 p = 1) : d2157 p ≤ (2 : Int) + d1895 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25545 p hg
    simpa only [d5540, d2157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25793 p hg
    simpa only [d5540, d2157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25795 (p : Pattern) (guard : d5540 p = 1) : d2158 p ≤ (2 : Int) + d6156 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2158, d6156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25794 p hg
    simpa only [d2158, d6156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2158, d6156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2158, d6156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25796 (p : Pattern) (guard : d5540 p = 1) : d3200 p ≤ (2 : Int) + d6195 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3200, d6195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25589 p hg
    simpa only [d3200, d6195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3200, d6195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25795 p hg
    simpa only [d3200, d6195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25797 (p : Pattern) (guard : d5540 p = 1) : d3201 p ≤ (2 : Int) + d6195 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25796 p hg
    simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25620 p hg
    simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25798 (p : Pattern) (guard : d5540 p = 1) : d3202 p ≤ (2 : Int) + d6303 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3202, d6303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25797 p hg
    simpa only [d3202, d6303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3202, d6303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25738 p hg
    simpa only [d3202, d6303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25799 (p : Pattern) (guard : d5540 p = 1) : d3203 p ≤ (2 : Int) + d6304 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3203, d6304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25798 p hg
    simpa only [d3203, d6304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3203, d6304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25635 p hg
    simpa only [d3203, d6304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25800 (p : Pattern) (guard : d5540 p = 1) : d3204 p ≤ (2 : Int) + d6305 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3204, d6305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25473 p hg
    simpa only [d3204, d6305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3204, d6305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3204, d6305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25801 (p : Pattern) (guard : d5540 p = 1) : d3205 p ≤ (2 : Int) + d6306 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3205, d6306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25800 p hg
    simpa only [d3205, d6306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3205, d6306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3205, d6306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25802 (p : Pattern) (guard : d5540 p = 1) : d3206 p ≤ (2 : Int) + d6307 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3206, d6307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25799 p hg
    simpa only [d3206, d6307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3206, d6307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25801 p hg
    simpa only [d3206, d6307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25803 (p : Pattern) (guard : d5540 p = 1) : d3207 p ≤ (2 : Int) + d6308 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3207, d6308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25792 p hg
    simpa only [d3207, d6308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3207, d6308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25802 p hg
    simpa only [d3207, d6308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25804 (p : Pattern) (guard : d5540 p = 1) : d3208 p ≤ (2 : Int) + d6309 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3208, d6309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25787 p hg
    simpa only [d3208, d6309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3208, d6309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25803 p hg
    simpa only [d3208, d6309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25805 (p : Pattern) (guard : d5540 p = 1) : d3209 p ≤ (2 : Int) + d6310 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3209, d6310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25620 p hg
    simpa only [d3209, d6310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3209, d6310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25472 p hg
    simpa only [d3209, d6310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25806 (p : Pattern) (guard : d5540 p = 1) : d3210 p ≤ (2 : Int) + d6311 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3210, d6311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25788 p hg
    simpa only [d3210, d6311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3210, d6311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25805 p hg
    simpa only [d3210, d6311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25807 (p : Pattern) (guard : d5540 p = 1) : d3211 p ≤ (2 : Int) + d6312 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3211, d6312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25615 p hg
    simpa only [d3211, d6312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3211, d6312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25472 p hg
    simpa only [d3211, d6312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25808 (p : Pattern) (guard : d5540 p = 1) : d3212 p ≤ (2 : Int) + d6313 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3212, d6313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25807 p hg
    simpa only [d3212, d6313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3212, d6313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3212, d6313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25809 (p : Pattern) (guard : d5540 p = 1) : d3213 p ≤ (2 : Int) + d6314 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3213, d6314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25806 p hg
    simpa only [d3213, d6314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3213, d6314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25808 p hg
    simpa only [d3213, d6314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25810 (p : Pattern) (guard : d5540 p = 1) : d3214 p ≤ (2 : Int) + d6315 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3214, d6315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25623 p hg
    simpa only [d3214, d6315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3214, d6315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25435 p hg
    simpa only [d3214, d6315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25811 (p : Pattern) (guard : d5540 p = 1) : d3215 p ≤ (2 : Int) + d6316 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3215, d6316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25810 p hg
    simpa only [d3215, d6316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3215, d6316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3215, d6316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25812 (p : Pattern) (guard : d5540 p = 1) : d3216 p ≤ (2 : Int) + d6317 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3216, d6317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25811 p hg
    simpa only [d3216, d6317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3216, d6317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3216, d6317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25813 (p : Pattern) (guard : d5540 p = 1) : d3217 p ≤ (2 : Int) + d6318 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3217, d6318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25809 p hg
    simpa only [d3217, d6318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3217, d6318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25812 p hg
    simpa only [d3217, d6318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25814 (p : Pattern) (guard : d5540 p = 1) : d3218 p ≤ (2 : Int) + d6319 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3218, d6319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25813 p hg
    simpa only [d3218, d6319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3218, d6319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25802 p hg
    simpa only [d3218, d6319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25815 (p : Pattern) (guard : d5540 p = 1) : d3219 p ≤ (2 : Int) + d6320 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3219, d6320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25814 p hg
    simpa only [d3219, d6320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3219, d6320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3219, d6320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25816 (p : Pattern) (guard : d5540 p = 1) : d3220 p ≤ (2 : Int) + d6321 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3220, d6321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25804 p hg
    simpa only [d3220, d6321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3220, d6321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25815 p hg
    simpa only [d3220, d6321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25817 (p : Pattern) (guard : d5540 p = 1) : d3221 p ≤ (2 : Int) + d6322 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3221, d6322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25746 p hg
    simpa only [d3221, d6322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3221, d6322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25816 p hg
    simpa only [d3221, d6322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25818 (p : Pattern) (guard : d5540 p = 1) : d3222 p ≤ (2 : Int) + d6323 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3222, d6323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d3222, d6323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3222, d6323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25817 p hg
    simpa only [d3222, d6323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25819 (p : Pattern) (guard : d5540 p = 1) : d3223 p ≤ (2 : Int) + d6324 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3223, d6324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25727 p hg
    simpa only [d3223, d6324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3223, d6324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25818 p hg
    simpa only [d3223, d6324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25820 (p : Pattern) (guard : d5540 p = 1) : d3224 p ≤ (2 : Int) + d6325 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3224, d6325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25650 p hg
    simpa only [d3224, d6325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3224, d6325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25819 p hg
    simpa only [d3224, d6325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25821 (p : Pattern) (guard : d5843 p = 1) : d14 p ≤ (0 : Int) + d3541 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19827 p hg
    simpa only [d3541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d3541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25822 (p : Pattern) (guard : d5843 p = 1) : d14 p ≤ (0 : Int) + d3542 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25821 p hg
    simpa only [d3542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d3542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25823 (p : Pattern) (guard : d5843 p = 1) : d1771 p ≤ (0 : Int) + d3544 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1771, d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d1771, d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1771, d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20514 p hg
    simpa only [d1771, d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25824 (p : Pattern) (guard : d5843 p = 1) : d1772 p ≤ (0 : Int) + d3545 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1772, d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25823 p hg
    simpa only [d1772, d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1772, d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20514 p hg
    simpa only [d1772, d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25825 (p : Pattern) (guard : d5843 p = 1) : d2895 p ≤ (0 : Int) + d3546 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2895, d3546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25822 p hg
    simpa only [d2895, d3546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2895, d3546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25824 p hg
    simpa only [d2895, d3546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25826 (p : Pattern) (guard : d5843 p = 1) : d1685 p ≤ (0 : Int) + d3548 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1685, d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d1685, d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1685, d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20520 p hg
    simpa only [d1685, d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25827 (p : Pattern) (guard : d5843 p = 1) : d1686 p ≤ (0 : Int) + d3549 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1686, d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25826 p hg
    simpa only [d1686, d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1686, d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20520 p hg
    simpa only [d1686, d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25828 (p : Pattern) (guard : d5843 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare25829 (p : Pattern) (guard : d5843 p = 1) : d1687 p ≤ (0 : Int) + d3550 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1687, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25827 p hg
    simpa only [d1687, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1687, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1687, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25830 (p : Pattern) (guard : d5843 p = 1) : d2896 p ≤ (0 : Int) + d3551 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2896, d3551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25825 p hg
    simpa only [d2896, d3551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2896, d3551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25829 p hg
    simpa only [d2896, d3551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25831 (p : Pattern) (guard : d5843 p = 1) : d2895 p ≤ (0 : Int) + d3552 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2895, d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d2895, d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2895, d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25824 p hg
    simpa only [d2895, d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25832 (p : Pattern) (guard : d5843 p = 1) : d2896 p ≤ (0 : Int) + d3553 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2896, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25831 p hg
    simpa only [d2896, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2896, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25829 p hg
    simpa only [d2896, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25833 (p : Pattern) (guard : d5843 p = 1) : d2896 p ≤ (0 : Int) + d3554 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25830 p hg
    simpa only [d3554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25832 p hg
    simpa only [d3554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25834 (p : Pattern) (guard : d5843 p = 1) : d2011 p ≤ (0 : Int) + d3556 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2011, d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19862 p hg
    simpa only [d2011, d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2011, d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20537 p hg
    simpa only [d2011, d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25835 (p : Pattern) (guard : d5843 p = 1) : d2012 p ≤ (0 : Int) + d3557 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2012, d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25834 p hg
    simpa only [d2012, d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2012, d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20537 p hg
    simpa only [d2012, d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25836 (p : Pattern) (guard : d5843 p = 1) : d2897 p ≤ (0 : Int) + d3558 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2897, d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19862 p hg
    simpa only [d2897, d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2897, d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25835 p hg
    simpa only [d2897, d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25837 (p : Pattern) (guard : d5843 p = 1) : d1695 p ≤ (0 : Int) + d3560 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1695, d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19862 p hg
    simpa only [d1695, d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1695, d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20543 p hg
    simpa only [d1695, d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25838 (p : Pattern) (guard : d5843 p = 1) : d1696 p ≤ (0 : Int) + d3561 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1696, d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25837 p hg
    simpa only [d1696, d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1696, d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20543 p hg
    simpa only [d1696, d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25839 (p : Pattern) (guard : d5843 p = 1) : d1697 p ≤ (0 : Int) + d3562 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1697, d3562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25838 p hg
    simpa only [d1697, d3562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1697, d3562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1697, d3562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25840 (p : Pattern) (guard : d5843 p = 1) : d2898 p ≤ (0 : Int) + d3563 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2898, d3563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25836 p hg
    simpa only [d2898, d3563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2898, d3563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25839 p hg
    simpa only [d2898, d3563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25841 (p : Pattern) (guard : d5843 p = 1) : d2899 p ≤ (0 : Int) + d3564 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2899, d3564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25832 p hg
    simpa only [d2899, d3564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2899, d3564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25840 p hg
    simpa only [d2899, d3564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25842 (p : Pattern) (guard : d5843 p = 1) : d2900 p ≤ (0 : Int) + d3565 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2900, d3565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25833 p hg
    simpa only [d2900, d3565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2900, d3565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25841 p hg
    simpa only [d2900, d3565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25843 (p : Pattern) (guard : d5843 p = 1) : d1802 p ≤ (0 : Int) + d3566 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1802, d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19890 p hg
    simpa only [d1802, d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1802, d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20552 p hg
    simpa only [d1802, d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25844 (p : Pattern) (guard : d5843 p = 1) : d1803 p ≤ (0 : Int) + d3567 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1803, d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25843 p hg
    simpa only [d1803, d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1803, d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20552 p hg
    simpa only [d1803, d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25845 (p : Pattern) (guard : d5843 p = 1) : d2901 p ≤ (0 : Int) + d3568 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2901, d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19890 p hg
    simpa only [d2901, d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2901, d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25844 p hg
    simpa only [d2901, d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25846 (p : Pattern) (guard : d5843 p = 1) : d1703 p ≤ (0 : Int) + d3570 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1703, d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19890 p hg
    simpa only [d1703, d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1703, d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20558 p hg
    simpa only [d1703, d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25847 (p : Pattern) (guard : d5843 p = 1) : d1704 p ≤ (0 : Int) + d3571 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1704, d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25846 p hg
    simpa only [d1704, d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1704, d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20558 p hg
    simpa only [d1704, d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25848 (p : Pattern) (guard : d5843 p = 1) : d1705 p ≤ (0 : Int) + d3572 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1705, d3572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25847 p hg
    simpa only [d1705, d3572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1705, d3572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1705, d3572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25849 (p : Pattern) (guard : d5843 p = 1) : d2902 p ≤ (0 : Int) + d3573 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2902, d3573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25845 p hg
    simpa only [d2902, d3573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2902, d3573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25848 p hg
    simpa only [d2902, d3573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25850 (p : Pattern) (guard : d5843 p = 1) : d2903 p ≤ (0 : Int) + d3574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2903, d3574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25849 p hg
    simpa only [d2903, d3574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2903, d3574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2903, d3574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25851 (p : Pattern) (guard : d5843 p = 1) : d2904 p ≤ (0 : Int) + d3575 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2904, d3575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25841 p hg
    simpa only [d2904, d3575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2904, d3575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25850 p hg
    simpa only [d2904, d3575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25852 (p : Pattern) (guard : d5843 p = 1) : d2905 p ≤ (0 : Int) + d3576 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2905, d3576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25842 p hg
    simpa only [d2905, d3576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2905, d3576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25851 p hg
    simpa only [d2905, d3576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25853 (p : Pattern) (guard : d5843 p = 1) : d1775 p ≤ (0 : Int) + d13 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1775, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d1775, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1775, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19926 p hg
    simpa only [d5843, d1775, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25854 (p : Pattern) (guard : d5843 p = 1) : d1776 p ≤ (0 : Int) + d3577 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1776, d3577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25853 p hg
    simpa only [d1776, d3577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1776, d3577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19928 p hg
    simpa only [d1776, d3577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25855 (p : Pattern) (guard : d5843 p = 1) : d1777 p ≤ (0 : Int) + d3578 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1777, d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d1777, d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1777, d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25854 p hg
    simpa only [d1777, d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25856 (p : Pattern) (guard : d5843 p = 1) : d1785 p ≤ (0 : Int) + d13 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1785, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d1785, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1785, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19937 p hg
    simpa only [d5843, d1785, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25857 (p : Pattern) (guard : d5843 p = 1) : d1786 p ≤ (0 : Int) + d3579 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1786, d3579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25856 p hg
    simpa only [d1786, d3579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1786, d3579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19889 p hg
    simpa only [d1786, d3579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25858 (p : Pattern) (guard : d5843 p = 1) : d1787 p ≤ (0 : Int) + d3580 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1787, d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20514 p hg
    simpa only [d1787, d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1787, d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25857 p hg
    simpa only [d1787, d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25859 (p : Pattern) (guard : d5843 p = 1) : d1788 p ≤ (0 : Int) + d3581 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1788, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25855 p hg
    simpa only [d1788, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1788, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25858 p hg
    simpa only [d1788, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25860 (p : Pattern) (guard : d5843 p = 1) : d2906 p ≤ (0 : Int) + d3582 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2906, d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d2906, d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2906, d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25859 p hg
    simpa only [d2906, d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25861 (p : Pattern) (guard : d5843 p = 1) : d1710 p ≤ (0 : Int) + d30 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1710, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5843, d1710, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1710, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20376 p hg
    simpa only [d5843, d1710, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25862 (p : Pattern) (guard : d5843 p = 1) : d1711 p ≤ (0 : Int) + d3583 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1711, d3583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25861 p hg
    simpa only [d1711, d3583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1711, d3583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20378 p hg
    simpa only [d1711, d3583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25863 (p : Pattern) (guard : d5843 p = 1) : d1712 p ≤ (0 : Int) + d3584 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1712, d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19918 p hg
    simpa only [d1712, d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1712, d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25862 p hg
    simpa only [d1712, d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25864 (p : Pattern) (guard : d5843 p = 1) : d1715 p ≤ (0 : Int) + d1715 p := by
  omega
theorem compare25865 (p : Pattern) (guard : d5843 p = 1) : d1716 p ≤ (0 : Int) + d3586 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1716, d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20575 p hg
    simpa only [d1716, d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1716, d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25864 p hg
    simpa only [d1716, d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25866 (p : Pattern) (guard : d5843 p = 1) : d1717 p ≤ (0 : Int) + d3587 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1717, d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25863 p hg
    simpa only [d1717, d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1717, d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25865 p hg
    simpa only [d1717, d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25867 (p : Pattern) (guard : d5843 p = 1) : d1718 p ≤ (0 : Int) + d3588 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1718, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25866 p hg
    simpa only [d1718, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1718, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1718, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25868 (p : Pattern) (guard : d5843 p = 1) : d2907 p ≤ (0 : Int) + d3589 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2907, d3589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25860 p hg
    simpa only [d2907, d3589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2907, d3589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25867 p hg
    simpa only [d2907, d3589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25869 (p : Pattern) (guard : d5843 p = 1) : d364 p ≤ (0 : Int) + d364 p := by
  omega
theorem compare25870 (p : Pattern) (guard : d5843 p = 1) : d1720 p ≤ (0 : Int) + d3590 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1720, d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19929 p hg
    simpa only [d1720, d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1720, d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25869 p hg
    simpa only [d1720, d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25871 (p : Pattern) (guard : d5843 p = 1) : d1723 p ≤ (0 : Int) + d3592 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1723, d3592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20584 p hg
    simpa only [d1723, d3592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1723, d3592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25869 p hg
    simpa only [d1723, d3592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25872 (p : Pattern) (guard : d5843 p = 1) : d1724 p ≤ (0 : Int) + d3593 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1724, d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25870 p hg
    simpa only [d1724, d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1724, d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25871 p hg
    simpa only [d1724, d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25873 (p : Pattern) (guard : d5843 p = 1) : d1725 p ≤ (0 : Int) + d3594 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1725, d3594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25872 p hg
    simpa only [d1725, d3594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1725, d3594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1725, d3594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25874 (p : Pattern) (guard : d5843 p = 1) : d2908 p ≤ (0 : Int) + d3595 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2908, d3595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25860 p hg
    simpa only [d2908, d3595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2908, d3595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25873 p hg
    simpa only [d2908, d3595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25875 (p : Pattern) (guard : d5843 p = 1) : d2909 p ≤ (0 : Int) + d3596 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2909, d3596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25868 p hg
    simpa only [d2909, d3596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2909, d3596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25874 p hg
    simpa only [d2909, d3596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25876 (p : Pattern) (guard : d5843 p = 1) : d1728 p ≤ (0 : Int) + d3597 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1728, d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19940 p hg
    simpa only [d1728, d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1728, d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20591 p hg
    simpa only [d1728, d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25877 (p : Pattern) (guard : d5843 p = 1) : d1729 p ≤ (0 : Int) + d3598 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1729, d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25876 p hg
    simpa only [d1729, d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1729, d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20591 p hg
    simpa only [d1729, d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25878 (p : Pattern) (guard : d5843 p = 1) : d1730 p ≤ (0 : Int) + d3599 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1730, d3599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25877 p hg
    simpa only [d1730, d3599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1730, d3599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d1730, d3599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25879 (p : Pattern) (guard : d5843 p = 1) : d2910 p ≤ (0 : Int) + d3600 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2910, d3600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25860 p hg
    simpa only [d2910, d3600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2910, d3600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25878 p hg
    simpa only [d2910, d3600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25880 (p : Pattern) (guard : d5843 p = 1) : d1791 p ≤ (0 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1791, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d5843, d1791, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1791, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19990 p hg
    simpa only [d5843, d1791, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25881 (p : Pattern) (guard : d5843 p = 1) : d1792 p ≤ (0 : Int) + d3601 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1792, d3601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25880 p hg
    simpa only [d1792, d3601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1792, d3601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19992 p hg
    simpa only [d1792, d3601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25882 (p : Pattern) (guard : d5843 p = 1) : d1793 p ≤ (0 : Int) + d3602 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1793, d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19862 p hg
    simpa only [d1793, d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1793, d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25881 p hg
    simpa only [d1793, d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25883 (p : Pattern) (guard : d5843 p = 1) : d339 p ≤ (0 : Int) + d339 p := by
  omega
theorem compare25884 (p : Pattern) (guard : d5843 p = 1) : d1796 p ≤ (0 : Int) + d3603 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1796, d3603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20537 p hg
    simpa only [d1796, d3603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1796, d3603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25883 p hg
    simpa only [d1796, d3603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25885 (p : Pattern) (guard : d5843 p = 1) : d1797 p ≤ (0 : Int) + d3604 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1797, d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25882 p hg
    simpa only [d1797, d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1797, d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25884 p hg
    simpa only [d1797, d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25886 (p : Pattern) (guard : d5843 p = 1) : d2911 p ≤ (0 : Int) + d3605 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2911, d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19862 p hg
    simpa only [d2911, d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2911, d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25885 p hg
    simpa only [d2911, d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25887 (p : Pattern) (guard : d5843 p = 1) : d2912 p ≤ (0 : Int) + d3606 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2912, d3606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25886 p hg
    simpa only [d2912, d3606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2912, d3606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2912, d3606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25888 (p : Pattern) (guard : d5843 p = 1) : d2913 p ≤ (0 : Int) + d3607 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2913, d3607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25879 p hg
    simpa only [d2913, d3607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2913, d3607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25887 p hg
    simpa only [d2913, d3607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25889 (p : Pattern) (guard : d5843 p = 1) : d2914 p ≤ (0 : Int) + d3608 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2914, d3608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25875 p hg
    simpa only [d2914, d3608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2914, d3608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25888 p hg
    simpa only [d2914, d3608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25890 (p : Pattern) (guard : d5843 p = 1) : d2915 p ≤ (0 : Int) + d3609 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2915, d3609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25860 p hg
    simpa only [d2915, d3609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2915, d3609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2915, d3609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25891 (p : Pattern) (guard : d5843 p = 1) : d2916 p ≤ (0 : Int) + d3610 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2916, d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25890 p hg
    simpa only [d2916, d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2916, d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25887 p hg
    simpa only [d2916, d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25892 (p : Pattern) (guard : d5843 p = 1) : d2917 p ≤ (0 : Int) + d3611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2917, d3611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25845 p hg
    simpa only [d2917, d3611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2917, d3611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2917, d3611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25893 (p : Pattern) (guard : d5843 p = 1) : d2918 p ≤ (0 : Int) + d3612 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2918, d3612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25892 p hg
    simpa only [d2918, d3612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2918, d3612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d2918, d3612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25894 (p : Pattern) (guard : d5843 p = 1) : d2919 p ≤ (0 : Int) + d3613 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2919, d3613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25891 p hg
    simpa only [d2919, d3613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2919, d3613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25893 p hg
    simpa only [d2919, d3613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25895 (p : Pattern) (guard : d5843 p = 1) : d2920 p ≤ (0 : Int) + d3614 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2920, d3614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25889 p hg
    simpa only [d2920, d3614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2920, d3614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25894 p hg
    simpa only [d2920, d3614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25896 (p : Pattern) (guard : d5843 p = 1) : d2921 p ≤ (0 : Int) + d3615 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2921, d3615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25852 p hg
    simpa only [d2921, d3615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2921, d3615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25895 p hg
    simpa only [d2921, d3615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25897 (p : Pattern) (guard : d5843 p = 1) : d14 p ≤ (0 : Int) + d3617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19964 p hg
    simpa only [d3617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d3617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25898 (p : Pattern) (guard : d5843 p = 1) : d14 p ≤ (0 : Int) + d3618 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25897 p hg
    simpa only [d3618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d3618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25899 (p : Pattern) (guard : d5843 p = 1) : d2895 p ≤ (0 : Int) + d3619 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2895, d3619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25898 p hg
    simpa only [d2895, d3619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2895, d3619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25824 p hg
    simpa only [d2895, d3619, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
