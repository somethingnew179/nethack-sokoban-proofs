/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons240
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare33740 (p : Pattern) (guard : d5843 p = 1) : d2136 p ≤ (2 : Int) + d8033 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2136, d8033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33528 p hg
    simpa only [d2136, d8033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2136, d8033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33739 p hg
    simpa only [d2136, d8033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33741 (p : Pattern) (guard : d5843 p = 1) : d3180 p ≤ (2 : Int) + d8034 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3180, d8034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33475 p hg
    simpa only [d3180, d8034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3180, d8034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33740 p hg
    simpa only [d3180, d8034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33742 (p : Pattern) (guard : d5843 p = 1) : d2131 p ≤ (2 : Int) + d8035 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2131, d8035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33480 p hg
    simpa only [d2131, d8035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2131, d8035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2131, d8035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33743 (p : Pattern) (guard : d5843 p = 1) : d3181 p ≤ (2 : Int) + d8036 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3181, d8036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33741 p hg
    simpa only [d3181, d8036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3181, d8036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33742 p hg
    simpa only [d3181, d8036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33744 (p : Pattern) (guard : d5843 p = 1) : d3182 p ≤ (2 : Int) + d8037 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3182, d8037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33743 p hg
    simpa only [d3182, d8037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3182, d8037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3182, d8037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33745 (p : Pattern) (guard : d5843 p = 1) : d3183 p ≤ (2 : Int) + d8038 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3183, d8038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33738 p hg
    simpa only [d3183, d8038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3183, d8038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33744 p hg
    simpa only [d3183, d8038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33746 (p : Pattern) (guard : d5843 p = 1) : d2137 p ≤ (2 : Int) + d8039 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2137, d8039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33740 p hg
    simpa only [d2137, d8039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2137, d8039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2137, d8039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33747 (p : Pattern) (guard : d5843 p = 1) : d3184 p ≤ (2 : Int) + d8040 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3184, d8040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33532 p hg
    simpa only [d3184, d8040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3184, d8040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33746 p hg
    simpa only [d3184, d8040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33748 (p : Pattern) (guard : d5843 p = 1) : d3185 p ≤ (2 : Int) + d8041 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3185, d8041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33747 p hg
    simpa only [d3185, d8041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3185, d8041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3185, d8041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33749 (p : Pattern) (guard : d5843 p = 1) : d3186 p ≤ (2 : Int) + d8042 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3186, d8042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33748 p hg
    simpa only [d3186, d8042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3186, d8042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3186, d8042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33750 (p : Pattern) (guard : d5843 p = 1) : d3187 p ≤ (2 : Int) + d8043 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3187, d8043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33745 p hg
    simpa only [d3187, d8043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3187, d8043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33749 p hg
    simpa only [d3187, d8043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33751 (p : Pattern) (guard : d5843 p = 1) : d3188 p ≤ (2 : Int) + d8044 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3188, d8044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33532 p hg
    simpa only [d3188, d8044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3188, d8044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33522 p hg
    simpa only [d3188, d8044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33752 (p : Pattern) (guard : d5843 p = 1) : d3189 p ≤ (2 : Int) + d8045 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3189, d8045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33751 p hg
    simpa only [d3189, d8045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3189, d8045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33533 p hg
    simpa only [d3189, d8045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33753 (p : Pattern) (guard : d5843 p = 1) : d3190 p ≤ (2 : Int) + d8046 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3190, d8046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33752 p hg
    simpa only [d3190, d8046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3190, d8046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33729 p hg
    simpa only [d3190, d8046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33754 (p : Pattern) (guard : d5843 p = 1) : d3191 p ≤ (2 : Int) + d8047 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3191, d8047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33353 p hg
    simpa only [d3191, d8047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3191, d8047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3191, d8047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33755 (p : Pattern) (guard : d5843 p = 1) : d3192 p ≤ (2 : Int) + d8048 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3192, d8048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33753 p hg
    simpa only [d3192, d8048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3192, d8048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33754 p hg
    simpa only [d3192, d8048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33756 (p : Pattern) (guard : d5843 p = 1) : d3193 p ≤ (2 : Int) + d8049 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3193, d8049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33750 p hg
    simpa only [d3193, d8049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3193, d8049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33755 p hg
    simpa only [d3193, d8049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33757 (p : Pattern) (guard : d5843 p = 1) : d3194 p ≤ (2 : Int) + d8050 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3194, d8050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33732 p hg
    simpa only [d3194, d8050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3194, d8050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33756 p hg
    simpa only [d3194, d8050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33758 (p : Pattern) (guard : d5843 p = 1) : d3195 p ≤ (2 : Int) + d8051 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3195, d8051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33580 p hg
    simpa only [d3195, d8051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3195, d8051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33583 p hg
    simpa only [d3195, d8051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33759 (p : Pattern) (guard : d5843 p = 1) : d3196 p ≤ (2 : Int) + d8052 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3196, d8052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33590 p hg
    simpa only [d3196, d8052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3196, d8052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33379 p hg
    simpa only [d3196, d8052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33760 (p : Pattern) (guard : d5843 p = 1) : d3197 p ≤ (2 : Int) + d8053 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3197, d8053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33758 p hg
    simpa only [d3197, d8053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3197, d8053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33759 p hg
    simpa only [d3197, d8053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33761 (p : Pattern) (guard : d5843 p = 1) : d3198 p ≤ (2 : Int) + d8054 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3198, d8054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33760 p hg
    simpa only [d3198, d8054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3198, d8054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33601 p hg
    simpa only [d3198, d8054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33762 (p : Pattern) (guard : d5843 p = 1) : d3199 p ≤ (2 : Int) + d8055 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3199, d8055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33761 p hg
    simpa only [d3199, d8055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3199, d8055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33605 p hg
    simpa only [d3199, d8055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33763 (p : Pattern) (guard : d5843 p = 1) : d2154 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4795 p hg
    simpa only [d5843, d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33289 p hg
    simpa only [d5843, d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33764 (p : Pattern) (guard : d5843 p = 1) : d2155 p ≤ (2 : Int) + d3257 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2155, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33763 p hg
    simpa only [d2155, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2155, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33291 p hg
    simpa only [d2155, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33765 (p : Pattern) (guard : d5843 p = 1) : d2156 p ≤ (2 : Int) + d8056 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2156, d8056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33508 p hg
    simpa only [d2156, d8056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2156, d8056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33764 p hg
    simpa only [d2156, d8056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33766 (p : Pattern) (guard : d5843 p = 1) : d2157 p ≤ (2 : Int) + d8057 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2157, d8057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33506 p hg
    simpa only [d2157, d8057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2157, d8057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33765 p hg
    simpa only [d2157, d8057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33767 (p : Pattern) (guard : d5843 p = 1) : d2158 p ≤ (2 : Int) + d8058 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2158, d8058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33766 p hg
    simpa only [d2158, d8058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2158, d8058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2158, d8058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33768 (p : Pattern) (guard : d5843 p = 1) : d3200 p ≤ (2 : Int) + d8059 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3200, d8059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33555 p hg
    simpa only [d3200, d8059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3200, d8059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33767 p hg
    simpa only [d3200, d8059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33769 (p : Pattern) (guard : d5843 p = 1) : d3201 p ≤ (2 : Int) + d8060 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3201, d8060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33768 p hg
    simpa only [d3201, d8060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3201, d8060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33590 p hg
    simpa only [d3201, d8060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33770 (p : Pattern) (guard : d5843 p = 1) : d3202 p ≤ (2 : Int) + d8061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3202, d8061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33769 p hg
    simpa only [d3202, d8061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3202, d8061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33708 p hg
    simpa only [d3202, d8061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33771 (p : Pattern) (guard : d5843 p = 1) : d3203 p ≤ (2 : Int) + d8062 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3203, d8062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33770 p hg
    simpa only [d3203, d8062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3203, d8062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33604 p hg
    simpa only [d3203, d8062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33772 (p : Pattern) (guard : d5843 p = 1) : d3204 p ≤ (2 : Int) + d8063 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3204, d8063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33421 p hg
    simpa only [d3204, d8063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3204, d8063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3204, d8063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33773 (p : Pattern) (guard : d5843 p = 1) : d3205 p ≤ (2 : Int) + d8064 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3205, d8064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33772 p hg
    simpa only [d3205, d8064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3205, d8064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3205, d8064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33774 (p : Pattern) (guard : d5843 p = 1) : d3206 p ≤ (2 : Int) + d8065 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3206, d8065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33771 p hg
    simpa only [d3206, d8065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3206, d8065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33773 p hg
    simpa only [d3206, d8065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33775 (p : Pattern) (guard : d5843 p = 1) : d3207 p ≤ (2 : Int) + d8066 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3207, d8066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33762 p hg
    simpa only [d3207, d8066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3207, d8066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33774 p hg
    simpa only [d3207, d8066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33776 (p : Pattern) (guard : d5843 p = 1) : d3208 p ≤ (2 : Int) + d8067 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3208, d8067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33757 p hg
    simpa only [d3208, d8067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3208, d8067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33775 p hg
    simpa only [d3208, d8067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33777 (p : Pattern) (guard : d5843 p = 1) : d3209 p ≤ (2 : Int) + d8068 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3209, d8068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33590 p hg
    simpa only [d3209, d8068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3209, d8068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33420 p hg
    simpa only [d3209, d8068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33778 (p : Pattern) (guard : d5843 p = 1) : d3210 p ≤ (2 : Int) + d8069 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3210, d8069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33758 p hg
    simpa only [d3210, d8069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3210, d8069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33777 p hg
    simpa only [d3210, d8069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33779 (p : Pattern) (guard : d5843 p = 1) : d3211 p ≤ (2 : Int) + d8070 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3211, d8070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33585 p hg
    simpa only [d3211, d8070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3211, d8070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33420 p hg
    simpa only [d3211, d8070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33780 (p : Pattern) (guard : d5843 p = 1) : d3212 p ≤ (2 : Int) + d8071 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3212, d8071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33779 p hg
    simpa only [d3212, d8071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3212, d8071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3212, d8071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33781 (p : Pattern) (guard : d5843 p = 1) : d3213 p ≤ (2 : Int) + d8072 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3213, d8072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33778 p hg
    simpa only [d3213, d8072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3213, d8072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33780 p hg
    simpa only [d3213, d8072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33782 (p : Pattern) (guard : d5843 p = 1) : d3214 p ≤ (2 : Int) + d8073 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3214, d8073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33592 p hg
    simpa only [d3214, d8073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3214, d8073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33379 p hg
    simpa only [d3214, d8073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33783 (p : Pattern) (guard : d5843 p = 1) : d3215 p ≤ (2 : Int) + d8074 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3215, d8074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33782 p hg
    simpa only [d3215, d8074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3215, d8074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3215, d8074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33784 (p : Pattern) (guard : d5843 p = 1) : d3216 p ≤ (2 : Int) + d8075 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3216, d8075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33783 p hg
    simpa only [d3216, d8075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3216, d8075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3216, d8075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33785 (p : Pattern) (guard : d5843 p = 1) : d3217 p ≤ (2 : Int) + d8076 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3217, d8076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33781 p hg
    simpa only [d3217, d8076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3217, d8076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33784 p hg
    simpa only [d3217, d8076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33786 (p : Pattern) (guard : d5843 p = 1) : d3218 p ≤ (2 : Int) + d8077 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3218, d8077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33785 p hg
    simpa only [d3218, d8077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3218, d8077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33774 p hg
    simpa only [d3218, d8077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33787 (p : Pattern) (guard : d5843 p = 1) : d3219 p ≤ (2 : Int) + d8078 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3219, d8078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33786 p hg
    simpa only [d3219, d8078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3219, d8078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d3219, d8078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33788 (p : Pattern) (guard : d5843 p = 1) : d3220 p ≤ (2 : Int) + d8079 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3220, d8079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33776 p hg
    simpa only [d3220, d8079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3220, d8079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33787 p hg
    simpa only [d3220, d8079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33789 (p : Pattern) (guard : d5843 p = 1) : d3221 p ≤ (2 : Int) + d8080 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3221, d8080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33716 p hg
    simpa only [d3221, d8080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3221, d8080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33788 p hg
    simpa only [d3221, d8080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33790 (p : Pattern) (guard : d5843 p = 1) : d3222 p ≤ (2 : Int) + d8081 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3222, d8081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33455 p hg
    simpa only [d3222, d8081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3222, d8081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33789 p hg
    simpa only [d3222, d8081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33791 (p : Pattern) (guard : d5843 p = 1) : d3223 p ≤ (2 : Int) + d8082 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3223, d8082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33697 p hg
    simpa only [d3223, d8082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3223, d8082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33790 p hg
    simpa only [d3223, d8082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33792 (p : Pattern) (guard : d5843 p = 1) : d3224 p ≤ (2 : Int) + d8083 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3224, d8083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33619 p hg
    simpa only [d3224, d8083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3224, d8083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33791 p hg
    simpa only [d3224, d8083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33793 (p : Pattern) (guard : d1 p = 1) : d3224 p ≤ (12 : Int) + d3224 p := by
  omega
theorem compare33794 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d313 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1518 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33795 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4499 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33796 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d314 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33794 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33795 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33797 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33795 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33798 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d316 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33796 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33797 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33799 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33800 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33799 p hg
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33801 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33800 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33802 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33798 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33801 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33803 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33797 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33804 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33803 p hg
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33805 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33802 p hg
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33804 p hg
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33806 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33801 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33807 (p : Pattern) (guard : d8086 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33808 (p : Pattern) (guard : d8087 p = 1) : d0 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33806 p hg
    simpa only [d8087, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33807 p hg
    simpa only [d8087, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33809 (p : Pattern) (guard : d8088 p = 1) : d0 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8088, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33805 p hg
    simpa only [d8088, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8087 p = 1 := by simpa only [d8088, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33808 p hg
    simpa only [d8088, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33810 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare889 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33811 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1492 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33812 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d326 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33810 p hg
    simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33811 p hg
    simpa only [d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33813 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33811 p hg
    simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33814 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33812 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33813 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33815 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d10 p := by
  change (0 : Int) ≤ (0 : Int) + 10
  decide
theorem compare33816 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33815 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33817 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33816 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33818 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33817 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33819 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33814 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33818 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33820 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33813 p hg
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33821 (p : Pattern) (guard : d8085 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33822 (p : Pattern) (guard : d8086 p = 1) : d0 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33820 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33821 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33823 (p : Pattern) (guard : d8087 p = 1) : d0 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33819 p hg
    simpa only [d8087, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d8087, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33824 (p : Pattern) (guard : d8086 p = 1) : d0 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33818 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33821 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33825 (p : Pattern) (guard : d8090 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33826 (p : Pattern) (guard : d8091 p = 1) : d0 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33827 (p : Pattern) (guard : d8092 p = 1) : d0 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33823 p hg
    simpa only [d8092, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d8092, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33828 (p : Pattern) (guard : d8093 p = 1) : d0 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8088 p = 1 := by simpa only [d8093, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33809 p hg
    simpa only [d8093, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8092 p = 1 := by simpa only [d8093, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33827 p hg
    simpa only [d8093, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33829 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1192 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33830 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d339 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33831 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33830 p hg
    simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33832 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33820 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33833 (p : Pattern) (guard : d8087 p = 1) : d0 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33832 p hg
    simpa only [d8087, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33807 p hg
    simpa only [d8087, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33834 (p : Pattern) (guard : d8091 p = 1) : d0 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33835 (p : Pattern) (guard : d8092 p = 1) : d0 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33833 p hg
    simpa only [d8092, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33834 p hg
    simpa only [d8092, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33836 (p : Pattern) (guard : d8086 p = 1) : d0 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33801 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33821 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33837 (p : Pattern) (guard : d8091 p = 1) : d0 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33836 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33838 (p : Pattern) (guard : d8095 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33839 (p : Pattern) (guard : d8096 p = 1) : d0 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33837 p hg
    simpa only [d8096, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33838 p hg
    simpa only [d8096, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33840 (p : Pattern) (guard : d8097 p = 1) : d0 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33835 p hg
    simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33839 p hg
    simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33841 (p : Pattern) (guard : d8098 p = 1) : d0 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8093 p = 1 := by simpa only [d8098, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33828 p hg
    simpa only [d8098, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8097 p = 1 := by simpa only [d8098, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33840 p hg
    simpa only [d8098, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33842 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare895 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33843 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33842 p hg
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33844 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33843 p hg
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33845 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33844 p hg
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33846 (p : Pattern) (guard : d8087 p = 1) : d0 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33845 p hg
    simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33807 p hg
    simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33847 (p : Pattern) (guard : d8091 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33848 (p : Pattern) (guard : d8092 p = 1) : d0 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33846 p hg
    simpa only [d8092, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33847 p hg
    simpa only [d8092, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33849 (p : Pattern) (guard : d8086 p = 1) : d0 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33803 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33821 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33850 (p : Pattern) (guard : d8091 p = 1) : d0 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33849 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33851 (p : Pattern) (guard : d8096 p = 1) : d0 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33850 p hg
    simpa only [d8096, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33838 p hg
    simpa only [d8096, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33852 (p : Pattern) (guard : d8097 p = 1) : d0 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33848 p hg
    simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33851 p hg
    simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33853 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1518 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33854 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33853 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33855 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33854 p hg
    simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33856 (p : Pattern) (guard : d8086 p = 1) : d0 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33855 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33821 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33857 (p : Pattern) (guard : d8091 p = 1) : d0 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33856 p hg
    simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33858 (p : Pattern) (guard : d8096 p = 1) : d0 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33857 p hg
    simpa only [d8096, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33838 p hg
    simpa only [d8096, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33859 (p : Pattern) (guard : d8101 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33860 (p : Pattern) (guard : d8102 p = 1) : d0 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33858 p hg
    simpa only [d8102, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33859 p hg
    simpa only [d8102, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33861 (p : Pattern) (guard : d8103 p = 1) : d0 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33852 p hg
    simpa only [d8103, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33860 p hg
    simpa only [d8103, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33862 (p : Pattern) (guard : d8104 p = 1) : d0 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8098 p = 1 := by simpa only [d8104, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33841 p hg
    simpa only [d8104, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8103 p = 1 := by simpa only [d8104, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33861 p hg
    simpa only [d8104, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33863 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1487 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33864 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33863 p hg
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33865 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33864 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33866 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33865 p hg
    simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33867 (p : Pattern) (guard : d8087 p = 1) : d0 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33866 p hg
    simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33807 p hg
    simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33868 (p : Pattern) (guard : d8092 p = 1) : d0 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33867 p hg
    simpa only [d8092, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33847 p hg
    simpa only [d8092, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33869 (p : Pattern) (guard : d8097 p = 1) : d0 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33868 p hg
    simpa only [d8097, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33858 p hg
    simpa only [d8097, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33870 (p : Pattern) (guard : d8096 p = 1) : d0 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d8096, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33838 p hg
    simpa only [d8096, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33871 (p : Pattern) (guard : d8102 p = 1) : d0 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d8102, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33859 p hg
    simpa only [d8102, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33872 (p : Pattern) (guard : d8103 p = 1) : d0 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33869 p hg
    simpa only [d8103, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33871 p hg
    simpa only [d8103, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33873 (p : Pattern) (guard : d8096 p = 1) : d0 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33834 p hg
    simpa only [d8096, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33838 p hg
    simpa only [d8096, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33874 (p : Pattern) (guard : d8102 p = 1) : d0 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33873 p hg
    simpa only [d8102, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33859 p hg
    simpa only [d8102, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33875 (p : Pattern) (guard : d8107 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare33876 (p : Pattern) (guard : d8108 p = 1) : d0 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d8108, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33875 p hg
    simpa only [d8108, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33877 (p : Pattern) (guard : d8109 p = 1) : d0 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33872 p hg
    simpa only [d8109, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33876 p hg
    simpa only [d8109, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33878 (p : Pattern) (guard : d8110 p = 1) : d0 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8104 p = 1 := by simpa only [d8110, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33862 p hg
    simpa only [d8110, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8109 p = 1 := by simpa only [d8110, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33877 p hg
    simpa only [d8110, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33879 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d378 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare779 p hg
    simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1492 p hg
    simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
