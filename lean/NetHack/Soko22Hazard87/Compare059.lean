import NetHack.Soko22Hazard87.Compare058
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare14750 (p : Pattern) (guard : d763 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14745 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14749 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14751 (p : Pattern) (guard : d764 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d764, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14750 p hg
    simpa only [d764, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14752 (p : Pattern) (guard : d765 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d765, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14751 p hg
    simpa only [d765, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14753 (p : Pattern) (guard : d16231 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16230 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14748 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14752 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14754 (p : Pattern) (guard : d16283 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16282 p = 1 := by simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14743 p hg
    simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16231 p = 1 := by simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14753 p hg
    simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14755 (p : Pattern) (guard : d16284 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16283 p = 1 := by simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14754 p hg
    simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14756 (p : Pattern) (guard : d16285 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16284 p = 1 := by simpa only [d16285, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14755 p hg
    simpa only [d16285, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16285, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d16285, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14757 (p : Pattern) (guard : d16286 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16286, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d16286, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16285 p = 1 := by simpa only [d16286, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14756 p hg
    simpa only [d16286, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14758 (p : Pattern) (guard : d767 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14752 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14759 (p : Pattern) (guard : d16232 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16231 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14753 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14758 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14760 (p : Pattern) (guard : d16233 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16232 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14759 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14761 (p : Pattern) (guard : d16234 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16233 p = 1 := by simpa only [d16234, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14760 p hg
    simpa only [d16234, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16234, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d16234, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14762 (p : Pattern) (guard : d16235 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16234 p = 1 := by simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14761 p hg
    simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14763 (p : Pattern) (guard : d16287 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16286 p = 1 := by simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14757 p hg
    simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16235 p = 1 := by simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14762 p hg
    simpa only [d16287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14764 (p : Pattern) (guard : d16288 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16287 p = 1 := by simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14763 p hg
    simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14765 (p : Pattern) (guard : d16289 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16288 p = 1 := by simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14764 p hg
    simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14766 (p : Pattern) (guard : d16330 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16289 p = 1 := by simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14765 p hg
    simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14767 (p : Pattern) (guard : d772 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14758 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14768 (p : Pattern) (guard : d773 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14767 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14769 (p : Pattern) (guard : d774 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14768 p hg
    simpa only [d774, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d774, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14770 (p : Pattern) (guard : d775 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14769 p hg
    simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14771 (p : Pattern) (guard : d16236 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14762 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14770 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14772 (p : Pattern) (guard : d16237 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16236 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14771 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14773 (p : Pattern) (guard : d16238 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16237 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14772 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14774 (p : Pattern) (guard : d16248 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16238 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14773 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14775 (p : Pattern) (guard : d16331 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16330 p = 1 := by simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14766 p hg
    simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16248 p = 1 := by simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14774 p hg
    simpa only [d16331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14776 (p : Pattern) (guard : d128275 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16331 p = 1 := by simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14775 p hg
    simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14777 (p : Pattern) (guard : d16311 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14762 p hg
    simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14778 (p : Pattern) (guard : d16312 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16311 p = 1 := by simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14777 p hg
    simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14779 (p : Pattern) (guard : d16313 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16312 p = 1 := by simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14778 p hg
    simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14780 (p : Pattern) (guard : d16335 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16313 p = 1 := by simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14779 p hg
    simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14781 (p : Pattern) (guard : d16336 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16335 p = 1 := by simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14780 p hg
    simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14782 (p : Pattern) (guard : d16337 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16336 p = 1 := by simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14781 p hg
    simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14783 (p : Pattern) (guard : d128276 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128275 p = 1 := by simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14776 p hg
    simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16337 p = 1 := by simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14782 p hg
    simpa only [d128276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14784 (p : Pattern) (guard : d128284 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128276 p = 1 := by simpa only [d128284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14783 p hg
    simpa only [d128284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14785 (p : Pattern) (guard : d128285 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128284 p = 1 := by simpa only [d128285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14784 p hg
    simpa only [d128285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14786 (p : Pattern) (guard : d128286 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128286, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128286, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128285 p = 1 := by simpa only [d128286, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14785 p hg
    simpa only [d128286, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14787 (p : Pattern) (guard : d128287 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128286 p = 1 := by simpa only [d128287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14786 p hg
    simpa only [d128287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14788 (p : Pattern) (guard : d780 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14770 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14789 (p : Pattern) (guard : d781 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14788 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14790 (p : Pattern) (guard : d782 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14789 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14791 (p : Pattern) (guard : d793 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d782 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14790 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14792 (p : Pattern) (guard : d945 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14791 p hg
    simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14793 (p : Pattern) (guard : d946 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d945 p = 1 := by simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14792 p hg
    simpa only [d946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14794 (p : Pattern) (guard : d947 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d946 p = 1 := by simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14793 p hg
    simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14795 (p : Pattern) (guard : d948 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d947 p = 1 := by simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14794 p hg
    simpa only [d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14796 (p : Pattern) (guard : d949 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d948 p = 1 := by simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14795 p hg
    simpa only [d949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14797 (p : Pattern) (guard : d959 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d959, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d959, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d949 p = 1 := by simpa only [d959, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14796 p hg
    simpa only [d959, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14798 (p : Pattern) (guard : d960 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d959 p = 1 := by simpa only [d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14797 p hg
    simpa only [d960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14799 (p : Pattern) (guard : d128288 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128287 p = 1 := by simpa only [d128288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14787 p hg
    simpa only [d128288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d960 p = 1 := by simpa only [d128288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14798 p hg
    simpa only [d128288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14800 (p : Pattern) (guard : d128289 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128288 p = 1 := by simpa only [d128289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14799 p hg
    simpa only [d128289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14801 (p : Pattern) (guard : d128290 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128289 p = 1 := by simpa only [d128290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14800 p hg
    simpa only [d128290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14802 (p : Pattern) (guard : d128291 p = 1) : d48359 p ≤ (1 : Int) + d171289 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128283 p = 1 := by simpa only [d128291, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14721 p hg
    simpa only [d128291, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128290 p = 1 := by simpa only [d128291, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14801 p hg
    simpa only [d128291, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14803 (p : Pattern) (guard : d967 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare14804 (p : Pattern) (guard : d968 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d967 p = 1 := by simpa only [d968, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14803 p hg
    simpa only [d968, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d968, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d968, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14805 (p : Pattern) (guard : d16358 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare14806 (p : Pattern) (guard : d16359 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16358 p = 1 := by simpa only [d16359, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14805 p hg
    simpa only [d16359, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16359, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d16359, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14807 (p : Pattern) (guard : d16360 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d968 p = 1 := by simpa only [d16360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14804 p hg
    simpa only [d16360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16359 p = 1 := by simpa only [d16360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14806 p hg
    simpa only [d16360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14808 (p : Pattern) (guard : d14646 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare14809 (p : Pattern) (guard : d14647 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14646 p = 1 := by simpa only [d14647, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14808 p hg
    simpa only [d14647, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14647, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d14647, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14810 (p : Pattern) (guard : d16361 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14647 p = 1 := by simpa only [d16361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14809 p hg
    simpa only [d16361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12861 p = 1 := by simpa only [d16361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14442 p hg
    simpa only [d16361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14811 (p : Pattern) (guard : d16362 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16360 p = 1 := by simpa only [d16362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14807 p hg
    simpa only [d16362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16361 p = 1 := by simpa only [d16362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14810 p hg
    simpa only [d16362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14812 (p : Pattern) (guard : d973 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare14813 (p : Pattern) (guard : d974 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d973 p = 1 := by simpa only [d974, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14812 p hg
    simpa only [d974, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d974, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d974, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14814 (p : Pattern) (guard : d12862 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12861 p = 1 := by simpa only [d12862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14442 p hg
    simpa only [d12862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d974 p = 1 := by simpa only [d12862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14813 p hg
    simpa only [d12862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14815 (p : Pattern) (guard : d16363 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16160 p = 1 := by simpa only [d16363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14440 p hg
    simpa only [d16363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12862 p = 1 := by simpa only [d16363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14814 p hg
    simpa only [d16363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14816 (p : Pattern) (guard : d16364 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16362 p = 1 := by simpa only [d16364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14811 p hg
    simpa only [d16364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16363 p = 1 := by simpa only [d16364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14815 p hg
    simpa only [d16364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14817 (p : Pattern) (guard : d16365 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16365, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d16365, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16364 p = 1 := by simpa only [d16365, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14816 p hg
    simpa only [d16365, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14818 (p : Pattern) (guard : d16366 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16366, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d16366, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16365 p = 1 := by simpa only [d16366, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14817 p hg
    simpa only [d16366, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14819 (p : Pattern) (guard : d980 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d974 p = 1 := by simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14813 p hg
    simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14820 (p : Pattern) (guard : d16367 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d12862 p = 1 := by simpa only [d16367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14814 p hg
    simpa only [d16367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d980 p = 1 := by simpa only [d16367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14819 p hg
    simpa only [d16367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14821 (p : Pattern) (guard : d16368 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16363 p = 1 := by simpa only [d16368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14815 p hg
    simpa only [d16368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16367 p = 1 := by simpa only [d16368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14820 p hg
    simpa only [d16368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14822 (p : Pattern) (guard : d16369 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16369, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d16369, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16368 p = 1 := by simpa only [d16369, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14821 p hg
    simpa only [d16369, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14823 (p : Pattern) (guard : d16370 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16370, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d16370, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16369 p = 1 := by simpa only [d16370, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14822 p hg
    simpa only [d16370, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14824 (p : Pattern) (guard : d16371 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16366 p = 1 := by simpa only [d16371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14818 p hg
    simpa only [d16371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16370 p = 1 := by simpa only [d16371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14823 p hg
    simpa only [d16371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14825 (p : Pattern) (guard : d975 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d415 p = 1 := by simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14128 p hg
    simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d974 p = 1 := by simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14813 p hg
    simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14826 (p : Pattern) (guard : d981 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d975 p = 1 := by simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14825 p hg
    simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d980 p = 1 := by simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14819 p hg
    simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14827 (p : Pattern) (guard : d16372 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16363 p = 1 := by simpa only [d16372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14815 p hg
    simpa only [d16372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d981 p = 1 := by simpa only [d16372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14826 p hg
    simpa only [d16372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14828 (p : Pattern) (guard : d16373 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16373, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d16373, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16372 p = 1 := by simpa only [d16373, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14827 p hg
    simpa only [d16373, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14829 (p : Pattern) (guard : d16374 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16374, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d16374, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16373 p = 1 := by simpa only [d16374, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14828 p hg
    simpa only [d16374, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14830 (p : Pattern) (guard : d986 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d980 p = 1 := by simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14819 p hg
    simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14831 (p : Pattern) (guard : d987 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d981 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14826 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14830 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14832 (p : Pattern) (guard : d988 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d988, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d988, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d988, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14831 p hg
    simpa only [d988, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14833 (p : Pattern) (guard : d989 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d989, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d989, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d988 p = 1 := by simpa only [d989, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14832 p hg
    simpa only [d989, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14834 (p : Pattern) (guard : d16375 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16374 p = 1 := by simpa only [d16375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14829 p hg
    simpa only [d16375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d989 p = 1 := by simpa only [d16375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14833 p hg
    simpa only [d16375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14835 (p : Pattern) (guard : d16376 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16371 p = 1 := by simpa only [d16376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14824 p hg
    simpa only [d16376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16375 p = 1 := by simpa only [d16376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14834 p hg
    simpa only [d16376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14836 (p : Pattern) (guard : d16377 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16376 p = 1 := by simpa only [d16377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d16377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d16377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14837 (p : Pattern) (guard : d16378 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16377 p = 1 := by simpa only [d16378, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14836 p hg
    simpa only [d16378, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16378, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d16378, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14838 (p : Pattern) (guard : d16379 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16379, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16379, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16378 p = 1 := by simpa only [d16379, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14837 p hg
    simpa only [d16379, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14839 (p : Pattern) (guard : d995 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d989 p = 1 := by simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14833 p hg
    simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14840 (p : Pattern) (guard : d16380 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16375 p = 1 := by simpa only [d16380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14834 p hg
    simpa only [d16380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d995 p = 1 := by simpa only [d16380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14839 p hg
    simpa only [d16380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14841 (p : Pattern) (guard : d16381 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16380 p = 1 := by simpa only [d16381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14840 p hg
    simpa only [d16381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d16381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14842 (p : Pattern) (guard : d16382 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16381 p = 1 := by simpa only [d16382, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d16382, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16382, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d16382, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14843 (p : Pattern) (guard : d16383 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16383, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16383, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16382 p = 1 := by simpa only [d16383, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14842 p hg
    simpa only [d16383, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14844 (p : Pattern) (guard : d16384 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16379 p = 1 := by simpa only [d16384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14838 p hg
    simpa only [d16384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16383 p = 1 := by simpa only [d16384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14843 p hg
    simpa only [d16384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14845 (p : Pattern) (guard : d16385 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16384 p = 1 := by simpa only [d16385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14844 p hg
    simpa only [d16385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14846 (p : Pattern) (guard : d16386 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16385 p = 1 := by simpa only [d16386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14845 p hg
    simpa only [d16386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14847 (p : Pattern) (guard : d16387 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16386 p = 1 := by simpa only [d16387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14846 p hg
    simpa only [d16387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14848 (p : Pattern) (guard : d1004 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d995 p = 1 := by simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14839 p hg
    simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14849 (p : Pattern) (guard : d1005 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1004 p = 1 := by simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14848 p hg
    simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14850 (p : Pattern) (guard : d1006 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1005 p = 1 := by simpa only [d1006, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14849 p hg
    simpa only [d1006, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1006, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d1006, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14851 (p : Pattern) (guard : d1007 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1007, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d1007, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1006 p = 1 := by simpa only [d1007, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14850 p hg
    simpa only [d1007, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14852 (p : Pattern) (guard : d16388 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16383 p = 1 := by simpa only [d16388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14843 p hg
    simpa only [d16388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1007 p = 1 := by simpa only [d16388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14851 p hg
    simpa only [d16388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14853 (p : Pattern) (guard : d16389 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16388 p = 1 := by simpa only [d16389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14852 p hg
    simpa only [d16389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14854 (p : Pattern) (guard : d16390 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16389 p = 1 := by simpa only [d16390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14853 p hg
    simpa only [d16390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14855 (p : Pattern) (guard : d16391 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16390 p = 1 := by simpa only [d16391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14854 p hg
    simpa only [d16391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14856 (p : Pattern) (guard : d16392 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16387 p = 1 := by simpa only [d16392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14847 p hg
    simpa only [d16392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16391 p = 1 := by simpa only [d16392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14855 p hg
    simpa only [d16392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14857 (p : Pattern) (guard : d128292 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16392 p = 1 := by simpa only [d128292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14856 p hg
    simpa only [d128292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14858 (p : Pattern) (guard : d16414 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16383 p = 1 := by simpa only [d16414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14843 p hg
    simpa only [d16414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14859 (p : Pattern) (guard : d16415 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16414 p = 1 := by simpa only [d16415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14858 p hg
    simpa only [d16415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14860 (p : Pattern) (guard : d16416 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16415 p = 1 := by simpa only [d16416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14859 p hg
    simpa only [d16416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14861 (p : Pattern) (guard : d16417 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16416 p = 1 := by simpa only [d16417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14860 p hg
    simpa only [d16417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14862 (p : Pattern) (guard : d16418 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16417 p = 1 := by simpa only [d16418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14861 p hg
    simpa only [d16418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14863 (p : Pattern) (guard : d16419 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16418 p = 1 := by simpa only [d16419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14862 p hg
    simpa only [d16419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14864 (p : Pattern) (guard : d128293 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128292 p = 1 := by simpa only [d128293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14857 p hg
    simpa only [d128293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16419 p = 1 := by simpa only [d128293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14863 p hg
    simpa only [d128293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14865 (p : Pattern) (guard : d128294 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128293 p = 1 := by simpa only [d128294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14864 p hg
    simpa only [d128294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14866 (p : Pattern) (guard : d128295 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128294 p = 1 := by simpa only [d128295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14865 p hg
    simpa only [d128295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14867 (p : Pattern) (guard : d128296 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128296, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128296, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128295 p = 1 := by simpa only [d128296, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14866 p hg
    simpa only [d128296, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14868 (p : Pattern) (guard : d128297 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128296 p = 1 := by simpa only [d128297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14867 p hg
    simpa only [d128297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14869 (p : Pattern) (guard : d1060 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1007 p = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14851 p hg
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14870 (p : Pattern) (guard : d1061 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1060 p = 1 := by simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14869 p hg
    simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14871 (p : Pattern) (guard : d1062 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1061 p = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14870 p hg
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14872 (p : Pattern) (guard : d1063 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1062 p = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14871 p hg
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14873 (p : Pattern) (guard : d1064 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1063 p = 1 := by simpa only [d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14872 p hg
    simpa only [d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14874 (p : Pattern) (guard : d1065 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1064 p = 1 := by simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14873 p hg
    simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14875 (p : Pattern) (guard : d1066 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1065 p = 1 := by simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14874 p hg
    simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14876 (p : Pattern) (guard : d1067 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1066 p = 1 := by simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14875 p hg
    simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14877 (p : Pattern) (guard : d1068 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1067 p = 1 := by simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14876 p hg
    simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14878 (p : Pattern) (guard : d1069 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1069, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d1069, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1068 p = 1 := by simpa only [d1069, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14877 p hg
    simpa only [d1069, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14879 (p : Pattern) (guard : d1070 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1069 p = 1 := by simpa only [d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14878 p hg
    simpa only [d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14880 (p : Pattern) (guard : d128298 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128297 p = 1 := by simpa only [d128298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14868 p hg
    simpa only [d128298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1070 p = 1 := by simpa only [d128298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14879 p hg
    simpa only [d128298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14881 (p : Pattern) (guard : d128299 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128298 p = 1 := by simpa only [d128299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14880 p hg
    simpa only [d128299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14882 (p : Pattern) (guard : d128300 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128299 p = 1 := by simpa only [d128300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14881 p hg
    simpa only [d128300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14883 (p : Pattern) (guard : d128301 p = 1) : d48387 p ≤ (1 : Int) + d171294 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128300 p = 1 := by simpa only [d128301, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14882 p hg
    simpa only [d128301, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128301, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13796 p hg
    simpa only [d128301, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14884 (p : Pattern) (guard : d128302 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 48 with
  | false =>
    have hg : d128291 p = 1 := by simpa only [d128302, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14802 p hg
    simpa only [d128302, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128301 p = 1 := by simpa only [d128302, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14883 p hg
    simpa only [d128302, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14885 (p : Pattern) (guard : d128303 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128302 p = 1 := by simpa only [d128303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14884 p hg
    simpa only [d128303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14886 (p : Pattern) (guard : d128304 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128303 p = 1 := by simpa only [d128304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14885 p hg
    simpa only [d128304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14887 (p : Pattern) (guard : d128305 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128304 p = 1 := by simpa only [d128305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14886 p hg
    simpa only [d128305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14888 (p : Pattern) (guard : d128306 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128305 p = 1 := by simpa only [d128306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14887 p hg
    simpa only [d128306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14889 (p : Pattern) (guard : d128307 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128306 p = 1 := by simpa only [d128307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14888 p hg
    simpa only [d128307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14890 (p : Pattern) (guard : d128308 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128307 p = 1 := by simpa only [d128308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14889 p hg
    simpa only [d128308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14891 (p : Pattern) (guard : d128309 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128308 p = 1 := by simpa only [d128309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14890 p hg
    simpa only [d128309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14892 (p : Pattern) (guard : d128310 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d128269 p = 1 := by simpa only [d128310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14509 p hg
    simpa only [d128310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128309 p = 1 := by simpa only [d128310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14891 p hg
    simpa only [d128310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14893 (p : Pattern) (guard : d1102 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare14894 (p : Pattern) (guard : d1103 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14893 p hg
    simpa only [d1103, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d1103, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14895 (p : Pattern) (guard : d16438 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare14896 (p : Pattern) (guard : d16439 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16438 p = 1 := by simpa only [d16439, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14895 p hg
    simpa only [d16439, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16439, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d16439, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14897 (p : Pattern) (guard : d16440 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14894 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16439 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14896 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14898 (p : Pattern) (guard : d14758 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare14899 (p : Pattern) (guard : d14759 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14758 p = 1 := by simpa only [d14759, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14898 p hg
    simpa only [d14759, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14759, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d14759, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14900 (p : Pattern) (guard : d14763 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare14901 (p : Pattern) (guard : d14764 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14763 p = 1 := by simpa only [d14764, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14900 p hg
    simpa only [d14764, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14764, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d14764, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14902 (p : Pattern) (guard : d16441 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14759 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14899 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14901 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14903 (p : Pattern) (guard : d16442 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16440 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14897 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16441 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14902 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14904 (p : Pattern) (guard : d1112 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare14905 (p : Pattern) (guard : d1113 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14904 p hg
    simpa only [d1113, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d1113, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14906 (p : Pattern) (guard : d1123 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare14907 (p : Pattern) (guard : d1124 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14906 p hg
    simpa only [d1124, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d1124, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14908 (p : Pattern) (guard : d1125 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14905 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14907 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14909 (p : Pattern) (guard : d14765 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14764 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14901 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14910 (p : Pattern) (guard : d16443 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14908 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14909 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14911 (p : Pattern) (guard : d16444 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14903 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16443 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14910 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14912 (p : Pattern) (guard : d16445 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16445, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16445, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16444 p = 1 := by simpa only [d16445, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14911 p hg
    simpa only [d16445, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14913 (p : Pattern) (guard : d16446 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16446, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16446, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16445 p = 1 := by simpa only [d16446, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14912 p hg
    simpa only [d16446, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14914 (p : Pattern) (guard : d5020 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare14915 (p : Pattern) (guard : d5021 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5020 p = 1 := by simpa only [d5021, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14914 p hg
    simpa only [d5021, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5021, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d5021, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14916 (p : Pattern) (guard : d5022 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5021 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14915 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14917 (p : Pattern) (guard : d14770 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare14918 (p : Pattern) (guard : d14771 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14770 p = 1 := by simpa only [d14771, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14917 p hg
    simpa only [d14771, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14771, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d14771, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14919 (p : Pattern) (guard : d14772 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14771 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14918 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14920 (p : Pattern) (guard : d14773 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5022 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14916 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14919 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14921 (p : Pattern) (guard : d16447 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14910 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14773 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14920 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14922 (p : Pattern) (guard : d16448 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16448, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16448, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16447 p = 1 := by simpa only [d16448, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14921 p hg
    simpa only [d16448, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14923 (p : Pattern) (guard : d16449 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16449, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16449, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16448 p = 1 := by simpa only [d16449, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14922 p hg
    simpa only [d16449, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14924 (p : Pattern) (guard : d16450 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16446 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14913 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16449 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14923 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14925 (p : Pattern) (guard : d1127 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14907 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14926 (p : Pattern) (guard : d14778 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14925 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14919 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14927 (p : Pattern) (guard : d16451 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14910 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14778 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14926 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14928 (p : Pattern) (guard : d16452 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16452, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16452, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16451 p = 1 := by simpa only [d16452, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14927 p hg
    simpa only [d16452, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14929 (p : Pattern) (guard : d16453 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16453, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16453, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16452 p = 1 := by simpa only [d16453, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14928 p hg
    simpa only [d16453, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14930 (p : Pattern) (guard : d16454 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16453 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14929 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14931 (p : Pattern) (guard : d16455 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14924 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16454 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14930 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14932 (p : Pattern) (guard : d16456 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16455 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14931 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14933 (p : Pattern) (guard : d16457 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16456 p = 1 := by simpa only [d16457, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14932 p hg
    simpa only [d16457, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16457, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16457, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14934 (p : Pattern) (guard : d16458 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16458, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16458, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16457 p = 1 := by simpa only [d16458, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14933 p hg
    simpa only [d16458, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14935 (p : Pattern) (guard : d16459 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16454 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14930 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14936 (p : Pattern) (guard : d16460 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16459 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14935 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14937 (p : Pattern) (guard : d16461 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16460 p = 1 := by simpa only [d16461, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14936 p hg
    simpa only [d16461, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16461, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16461, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14938 (p : Pattern) (guard : d16462 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16462, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16462, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16461 p = 1 := by simpa only [d16462, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14937 p hg
    simpa only [d16462, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14939 (p : Pattern) (guard : d16463 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16458 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14934 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14938 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14940 (p : Pattern) (guard : d16464 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16463 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14939 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14941 (p : Pattern) (guard : d16465 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16464 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14940 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14942 (p : Pattern) (guard : d16466 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16465 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14941 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14943 (p : Pattern) (guard : d16467 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16462 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14938 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14944 (p : Pattern) (guard : d16468 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16467 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14943 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14945 (p : Pattern) (guard : d16469 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16468 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14944 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14946 (p : Pattern) (guard : d16470 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16469 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14945 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14947 (p : Pattern) (guard : d16471 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16466 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14942 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16470 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14946 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14948 (p : Pattern) (guard : d16472 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16471 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14947 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14949 (p : Pattern) (guard : d16473 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16472 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14948 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14950 (p : Pattern) (guard : d16474 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16473 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14949 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14951 (p : Pattern) (guard : d16475 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16474 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14950 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14952 (p : Pattern) (guard : d16476 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16475 p = 1 := by simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14951 p hg
    simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14953 (p : Pattern) (guard : d16477 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d16477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16476 p = 1 := by simpa only [d16477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14952 p hg
    simpa only [d16477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14954 (p : Pattern) (guard : d16478 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16477 p = 1 := by simpa only [d16478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14953 p hg
    simpa only [d16478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d16478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14955 (p : Pattern) (guard : d16446 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16446, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16446, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16445 p = 1 := by simpa only [d16446, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14912 p hg
    simpa only [d16446, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14956 (p : Pattern) (guard : d16449 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16449, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16449, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16448 p = 1 := by simpa only [d16449, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14922 p hg
    simpa only [d16449, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14957 (p : Pattern) (guard : d16450 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16446 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14955 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16449 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14956 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14958 (p : Pattern) (guard : d16453 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16453, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16453, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16452 p = 1 := by simpa only [d16453, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14928 p hg
    simpa only [d16453, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14959 (p : Pattern) (guard : d16454 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16453 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14958 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14960 (p : Pattern) (guard : d16455 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14957 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16454 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14959 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14961 (p : Pattern) (guard : d16456 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16455 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14960 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14962 (p : Pattern) (guard : d16457 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16456 p = 1 := by simpa only [d16457, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14961 p hg
    simpa only [d16457, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16457, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16457, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14963 (p : Pattern) (guard : d16458 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16458, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d16458, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16457 p = 1 := by simpa only [d16458, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14962 p hg
    simpa only [d16458, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14964 (p : Pattern) (guard : d16459 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16454 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14959 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14965 (p : Pattern) (guard : d16460 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16459 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14964 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14966 (p : Pattern) (guard : d16461 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16460 p = 1 := by simpa only [d16461, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14965 p hg
    simpa only [d16461, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16461, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16461, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14967 (p : Pattern) (guard : d16462 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16462, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d16462, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16461 p = 1 := by simpa only [d16462, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14966 p hg
    simpa only [d16462, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14968 (p : Pattern) (guard : d16463 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16458 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14963 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14967 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14969 (p : Pattern) (guard : d16464 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16463 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14968 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14970 (p : Pattern) (guard : d16465 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16464 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14969 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14971 (p : Pattern) (guard : d16466 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16465 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14970 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14972 (p : Pattern) (guard : d16467 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16462 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14967 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14973 (p : Pattern) (guard : d16468 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16467 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14972 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14974 (p : Pattern) (guard : d16469 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16468 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14973 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14975 (p : Pattern) (guard : d16470 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16469 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14974 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14976 (p : Pattern) (guard : d16471 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16466 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14971 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16470 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14975 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14977 (p : Pattern) (guard : d16472 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16471 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14976 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14978 (p : Pattern) (guard : d16473 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16472 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14977 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14979 (p : Pattern) (guard : d16474 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16473 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14978 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14980 (p : Pattern) (guard : d16475 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16474 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14979 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14981 (p : Pattern) (guard : d16479 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16465 p = 1 := by simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14941 p hg
    simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14982 (p : Pattern) (guard : d16480 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16469 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14945 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14983 (p : Pattern) (guard : d16481 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16479 p = 1 := by simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14981 p hg
    simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16480 p = 1 := by simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14982 p hg
    simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14984 (p : Pattern) (guard : d16482 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16481 p = 1 := by simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14983 p hg
    simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14985 (p : Pattern) (guard : d16483 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16482 p = 1 := by simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14984 p hg
    simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14986 (p : Pattern) (guard : d16484 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16483 p = 1 := by simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14985 p hg
    simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14987 (p : Pattern) (guard : d16485 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16484 p = 1 := by simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14986 p hg
    simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14988 (p : Pattern) (guard : d16486 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16475 p = 1 := by simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14980 p hg
    simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16485 p = 1 := by simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14987 p hg
    simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14989 (p : Pattern) (guard : d16487 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16476 p = 1 := by simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14952 p hg
    simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16486 p = 1 := by simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14988 p hg
    simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14990 (p : Pattern) (guard : d16488 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16487 p = 1 := by simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14989 p hg
    simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14991 (p : Pattern) (guard : d16489 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16478 p = 1 := by simpa only [d16489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14954 p hg
    simpa only [d16489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16488 p = 1 := by simpa only [d16489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14990 p hg
    simpa only [d16489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14992 (p : Pattern) (guard : d16490 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16464 p = 1 := by simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14940 p hg
    simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14993 (p : Pattern) (guard : d16491 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16490 p = 1 := by simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14992 p hg
    simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14994 (p : Pattern) (guard : d16492 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16468 p = 1 := by simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14944 p hg
    simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14995 (p : Pattern) (guard : d16493 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16492 p = 1 := by simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14994 p hg
    simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14996 (p : Pattern) (guard : d16494 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16491 p = 1 := by simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14993 p hg
    simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16493 p = 1 := by simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14995 p hg
    simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14997 (p : Pattern) (guard : d16495 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16494 p = 1 := by simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14996 p hg
    simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14998 (p : Pattern) (guard : d16496 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16495 p = 1 := by simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14997 p hg
    simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14999 (p : Pattern) (guard : d16497 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16496 p = 1 := by simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14998 p hg
    simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
