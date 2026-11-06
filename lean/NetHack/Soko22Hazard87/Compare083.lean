import NetHack.Soko22Hazard87.Compare082
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare20750 (p : Pattern) (guard : d764 p = 1) : d48326 p ≤ (0 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20392 p hg
    simpa only [d764, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20749 p hg
    simpa only [d764, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20751 (p : Pattern) (guard : d765 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20391 p hg
    simpa only [d765, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20750 p hg
    simpa only [d765, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20752 (p : Pattern) (guard : d16231 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16230 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20747 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20751 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20753 (p : Pattern) (guard : d767 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20751 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20754 (p : Pattern) (guard : d16232 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16231 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20752 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20753 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20755 (p : Pattern) (guard : d16233 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16232 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20754 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20756 (p : Pattern) (guard : d16234 p = 1) : d48338 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16233 p = 1 := by simpa only [d16234, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20755 p hg
    simpa only [d16234, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16234, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d16234, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20757 (p : Pattern) (guard : d16235 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16235, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20390 p hg
    simpa only [d16235, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16234 p = 1 := by simpa only [d16235, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20756 p hg
    simpa only [d16235, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20758 (p : Pattern) (guard : d772 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20753 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20759 (p : Pattern) (guard : d773 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20758 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20760 (p : Pattern) (guard : d774 p = 1) : d48338 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20759 p hg
    simpa only [d774, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d774, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20761 (p : Pattern) (guard : d775 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20390 p hg
    simpa only [d775, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20760 p hg
    simpa only [d775, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20762 (p : Pattern) (guard : d16236 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20757 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20761 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20763 (p : Pattern) (guard : d16237 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16236 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20762 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20764 (p : Pattern) (guard : d16238 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16237 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20763 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20765 (p : Pattern) (guard : d16239 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16238 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20764 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20766 (p : Pattern) (guard : d780 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20761 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20767 (p : Pattern) (guard : d781 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20766 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20768 (p : Pattern) (guard : d782 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20767 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20769 (p : Pattern) (guard : d783 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d782 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20768 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20770 (p : Pattern) (guard : d16240 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16239 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20765 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d783 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20769 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20771 (p : Pattern) (guard : d16241 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16240 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20770 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20772 (p : Pattern) (guard : d16242 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16241 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20771 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20773 (p : Pattern) (guard : d16243 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16242 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20772 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20774 (p : Pattern) (guard : d16244 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16243 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20773 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20775 (p : Pattern) (guard : d16245 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16244 p = 1 := by simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20774 p hg
    simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20776 (p : Pattern) (guard : d16230 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16230, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20426 p hg
    simpa only [d16230, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16229 p = 1 := by simpa only [d16230, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20746 p hg
    simpa only [d16230, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20777 (p : Pattern) (guard : d765 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20426 p hg
    simpa only [d765, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20750 p hg
    simpa only [d765, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20778 (p : Pattern) (guard : d16231 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16230 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20776 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20777 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20779 (p : Pattern) (guard : d767 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20777 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20780 (p : Pattern) (guard : d16232 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16231 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20778 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20779 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20781 (p : Pattern) (guard : d16233 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16232 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20780 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20782 (p : Pattern) (guard : d16234 p = 1) : d48329 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16233 p = 1 := by simpa only [d16234, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20781 p hg
    simpa only [d16234, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16234, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d16234, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20783 (p : Pattern) (guard : d16235 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16235, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20425 p hg
    simpa only [d16235, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16234 p = 1 := by simpa only [d16235, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20782 p hg
    simpa only [d16235, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20784 (p : Pattern) (guard : d772 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20779 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20785 (p : Pattern) (guard : d773 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20784 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20786 (p : Pattern) (guard : d774 p = 1) : d48329 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20785 p hg
    simpa only [d774, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d774, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20787 (p : Pattern) (guard : d775 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20425 p hg
    simpa only [d775, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20786 p hg
    simpa only [d775, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20788 (p : Pattern) (guard : d16236 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20783 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20787 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20789 (p : Pattern) (guard : d16237 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16236 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20788 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20790 (p : Pattern) (guard : d16238 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16237 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20789 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20791 (p : Pattern) (guard : d16239 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16238 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20790 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20792 (p : Pattern) (guard : d780 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20787 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20793 (p : Pattern) (guard : d781 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20792 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20794 (p : Pattern) (guard : d782 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20793 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20795 (p : Pattern) (guard : d783 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d782 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20794 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20796 (p : Pattern) (guard : d16240 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16239 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20791 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d783 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20795 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20797 (p : Pattern) (guard : d16241 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16240 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20796 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20798 (p : Pattern) (guard : d16242 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16241 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20797 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20799 (p : Pattern) (guard : d16243 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16242 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20798 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20800 (p : Pattern) (guard : d16244 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16243 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20799 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20801 (p : Pattern) (guard : d16248 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16238 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20764 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20802 (p : Pattern) (guard : d793 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d782 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20768 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20803 (p : Pattern) (guard : d16249 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16248 p = 1 := by simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20801 p hg
    simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20802 p hg
    simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20804 (p : Pattern) (guard : d16250 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16249 p = 1 := by simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20803 p hg
    simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20805 (p : Pattern) (guard : d16251 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16250 p = 1 := by simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20804 p hg
    simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20806 (p : Pattern) (guard : d16252 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16251 p = 1 := by simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20805 p hg
    simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20807 (p : Pattern) (guard : d16253 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16252 p = 1 := by simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20806 p hg
    simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20808 (p : Pattern) (guard : d16254 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16244 p = 1 := by simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20800 p hg
    simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16253 p = 1 := by simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20807 p hg
    simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20809 (p : Pattern) (guard : d16255 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16245 p = 1 := by simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20775 p hg
    simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16254 p = 1 := by simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20808 p hg
    simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20810 (p : Pattern) (guard : d16256 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16255 p = 1 := by simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20809 p hg
    simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20811 (p : Pattern) (guard : d171103 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16256 p = 1 := by simpa only [d171103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20810 p hg
    simpa only [d171103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d171103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20812 (p : Pattern) (guard : d171104 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d171104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171103 p = 1 := by simpa only [d171104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20811 p hg
    simpa only [d171104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20813 (p : Pattern) (guard : d542 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare20814 (p : Pattern) (guard : d543 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20813 p hg
    simpa only [d543, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d543, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20815 (p : Pattern) (guard : d544 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20814 p hg
    simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20816 (p : Pattern) (guard : d545 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20815 p hg
    simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20817 (p : Pattern) (guard : d546 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20816 p hg
    simpa only [d546, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d546, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20818 (p : Pattern) (guard : d9457 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare20819 (p : Pattern) (guard : d9458 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9457 p = 1 := by simpa only [d9458, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20818 p hg
    simpa only [d9458, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9458, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d9458, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20820 (p : Pattern) (guard : d9460 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9458 p = 1 := by simpa only [d9460, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20819 p hg
    simpa only [d9460, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9460, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d9460, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20821 (p : Pattern) (guard : d16073 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16073, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d16073, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9460 p = 1 := by simpa only [d16073, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20820 p hg
    simpa only [d16073, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20822 (p : Pattern) (guard : d16074 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16073 p = 1 := by simpa only [d16074, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20821 p hg
    simpa only [d16074, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16074, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d16074, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20823 (p : Pattern) (guard : d16075 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20817 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16074 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20822 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20824 (p : Pattern) (guard : d9467 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare20825 (p : Pattern) (guard : d9468 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9467 p = 1 := by simpa only [d9468, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20824 p hg
    simpa only [d9468, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9468, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d9468, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20826 (p : Pattern) (guard : d9470 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9468 p = 1 := by simpa only [d9470, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20825 p hg
    simpa only [d9470, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9470, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d9470, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20827 (p : Pattern) (guard : d12748 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12748, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d12748, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9470 p = 1 := by simpa only [d12748, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20826 p hg
    simpa only [d12748, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20828 (p : Pattern) (guard : d12749 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12748 p = 1 := by simpa only [d12749, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20827 p hg
    simpa only [d12749, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12749, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d12749, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20829 (p : Pattern) (guard : d750 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare20830 (p : Pattern) (guard : d751 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20829 p hg
    simpa only [d751, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d751, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20831 (p : Pattern) (guard : d752 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20830 p hg
    simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20832 (p : Pattern) (guard : d753 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20831 p hg
    simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20833 (p : Pattern) (guard : d754 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20832 p hg
    simpa only [d754, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d754, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20834 (p : Pattern) (guard : d12750 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20828 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20833 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20835 (p : Pattern) (guard : d16227 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20823 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12750 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20834 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20836 (p : Pattern) (guard : d755 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20670 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20833 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20837 (p : Pattern) (guard : d757 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20833 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20838 (p : Pattern) (guard : d758 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20836 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20837 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20839 (p : Pattern) (guard : d16228 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20835 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20838 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20840 (p : Pattern) (guard : d16229 p = 1) : d48346 p ≤ (0 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16229, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20458 p hg
    simpa only [d16229, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16228 p = 1 := by simpa only [d16229, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20839 p hg
    simpa only [d16229, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20841 (p : Pattern) (guard : d16230 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16230, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d16230, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16229 p = 1 := by simpa only [d16230, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20840 p hg
    simpa only [d16230, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20842 (p : Pattern) (guard : d762 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20837 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20843 (p : Pattern) (guard : d763 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20838 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20842 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20844 (p : Pattern) (guard : d764 p = 1) : d48346 p ≤ (0 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20458 p hg
    simpa only [d764, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20843 p hg
    simpa only [d764, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20845 (p : Pattern) (guard : d765 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d765, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20844 p hg
    simpa only [d765, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20846 (p : Pattern) (guard : d16231 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16230 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20841 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20845 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20847 (p : Pattern) (guard : d767 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20845 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20848 (p : Pattern) (guard : d16232 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16231 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20846 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20847 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20849 (p : Pattern) (guard : d16233 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16232 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20848 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20850 (p : Pattern) (guard : d16234 p = 1) : d48356 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16233 p = 1 := by simpa only [d16234, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20849 p hg
    simpa only [d16234, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16234, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20477 p hg
    simpa only [d16234, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20851 (p : Pattern) (guard : d16235 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20456 p hg
    simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16234 p = 1 := by simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20850 p hg
    simpa only [d16235, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20852 (p : Pattern) (guard : d772 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20847 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20853 (p : Pattern) (guard : d773 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20852 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20854 (p : Pattern) (guard : d774 p = 1) : d48356 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20853 p hg
    simpa only [d774, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20477 p hg
    simpa only [d774, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20855 (p : Pattern) (guard : d775 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20456 p hg
    simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20854 p hg
    simpa only [d775, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20856 (p : Pattern) (guard : d16236 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20851 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20855 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20857 (p : Pattern) (guard : d16237 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16236 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20856 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20858 (p : Pattern) (guard : d16238 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16237 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20857 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20859 (p : Pattern) (guard : d16248 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16238 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20858 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20860 (p : Pattern) (guard : d780 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20855 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20861 (p : Pattern) (guard : d781 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20860 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20862 (p : Pattern) (guard : d782 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20861 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20863 (p : Pattern) (guard : d793 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d782 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20862 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20864 (p : Pattern) (guard : d16249 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16248 p = 1 := by simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20859 p hg
    simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20863 p hg
    simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20865 (p : Pattern) (guard : d16250 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16249 p = 1 := by simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20864 p hg
    simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20866 (p : Pattern) (guard : d16251 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16250 p = 1 := by simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20865 p hg
    simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20867 (p : Pattern) (guard : d16252 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16251 p = 1 := by simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20866 p hg
    simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20868 (p : Pattern) (guard : d16253 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16252 p = 1 := by simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20867 p hg
    simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20869 (p : Pattern) (guard : d171105 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171105, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d171105, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16253 p = 1 := by simpa only [d171105, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20868 p hg
    simpa only [d171105, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20870 (p : Pattern) (guard : d171106 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171105 p = 1 := by simpa only [d171106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20869 p hg
    simpa only [d171106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20871 (p : Pattern) (guard : d171107 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 69 with
  | false =>
    have hg : d171106 p = 1 := by simpa only [d171107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20870 p hg
    simpa only [d171107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20872 (p : Pattern) (guard : d171108 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 51 with
  | false =>
    have hg : d171107 p = 1 := by simpa only [d171108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20871 p hg
    simpa only [d171108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20873 (p : Pattern) (guard : d171109 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 50 with
  | false =>
    have hg : d171108 p = 1 := by simpa only [d171109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20872 p hg
    simpa only [d171109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20874 (p : Pattern) (guard : d171110 p = 1) : d48359 p ≤ (0 : Int) + d173727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d171104 p = 1 := by simpa only [d171110, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20812 p hg
    simpa only [d171110, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171109 p = 1 := by simpa only [d171110, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20873 p hg
    simpa only [d171110, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20875 (p : Pattern) (guard : d175671 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 48 with
  | false =>
    have hg : d171110 p = 1 := by simpa only [d175671, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20874 p hg
    simpa only [d175671, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175671, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20495 p hg
    simpa only [d175671, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20876 (p : Pattern) (guard : d175672 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175671 p = 1 := by simpa only [d175672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20875 p hg
    simpa only [d175672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20877 (p : Pattern) (guard : d175673 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175672 p = 1 := by simpa only [d175673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20876 p hg
    simpa only [d175673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20878 (p : Pattern) (guard : d175674 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175673 p = 1 := by simpa only [d175674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20877 p hg
    simpa only [d175674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20879 (p : Pattern) (guard : d175675 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175674 p = 1 := by simpa only [d175675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20878 p hg
    simpa only [d175675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20880 (p : Pattern) (guard : d175676 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175675 p = 1 := by simpa only [d175676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20879 p hg
    simpa only [d175676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20881 (p : Pattern) (guard : d175677 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175676 p = 1 := by simpa only [d175677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20880 p hg
    simpa only [d175677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20882 (p : Pattern) (guard : d175678 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175677 p = 1 := by simpa only [d175678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20881 p hg
    simpa only [d175678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20883 (p : Pattern) (guard : d175679 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d175670 p = 1 := by simpa only [d175679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20718 p hg
    simpa only [d175679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175678 p = 1 := by simpa only [d175679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20882 p hg
    simpa only [d175679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20884 (p : Pattern) (guard : d1099 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20885 (p : Pattern) (guard : d1100 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20884 p hg
    simpa only [d1100, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d1100, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20886 (p : Pattern) (guard : d1101 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20885 p hg
    simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20887 (p : Pattern) (guard : d1102 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d1102, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20886 p hg
    simpa only [d1102, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20888 (p : Pattern) (guard : d1103 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20887 p hg
    simpa only [d1103, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d1103, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20889 (p : Pattern) (guard : d9788 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20890 (p : Pattern) (guard : d9789 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9788 p = 1 := by simpa only [d9789, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20889 p hg
    simpa only [d9789, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9789, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d9789, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20891 (p : Pattern) (guard : d9791 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9789 p = 1 := by simpa only [d9791, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20890 p hg
    simpa only [d9791, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9791, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d9791, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20892 (p : Pattern) (guard : d16438 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16438, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d16438, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9791 p = 1 := by simpa only [d16438, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20891 p hg
    simpa only [d16438, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20893 (p : Pattern) (guard : d16439 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16438 p = 1 := by simpa only [d16439, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20892 p hg
    simpa only [d16439, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16439, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d16439, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20894 (p : Pattern) (guard : d16440 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20888 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16439 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20893 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20895 (p : Pattern) (guard : d9777 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20896 (p : Pattern) (guard : d9778 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9777 p = 1 := by simpa only [d9778, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20895 p hg
    simpa only [d9778, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9778, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d9778, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20897 (p : Pattern) (guard : d9780 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9778 p = 1 := by simpa only [d9780, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20896 p hg
    simpa only [d9780, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9780, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d9780, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20898 (p : Pattern) (guard : d14758 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14758, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d14758, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9780 p = 1 := by simpa only [d14758, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20897 p hg
    simpa only [d14758, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20899 (p : Pattern) (guard : d14759 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14758 p = 1 := by simpa only [d14759, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20898 p hg
    simpa only [d14759, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14759, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d14759, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20900 (p : Pattern) (guard : d9799 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20901 (p : Pattern) (guard : d9800 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9799 p = 1 := by simpa only [d9800, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20900 p hg
    simpa only [d9800, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9800, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d9800, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20902 (p : Pattern) (guard : d9802 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9800 p = 1 := by simpa only [d9802, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20901 p hg
    simpa only [d9802, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9802, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d9802, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20903 (p : Pattern) (guard : d14763 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14763, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d14763, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9802 p = 1 := by simpa only [d14763, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20902 p hg
    simpa only [d14763, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20904 (p : Pattern) (guard : d14764 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14763 p = 1 := by simpa only [d14764, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20903 p hg
    simpa only [d14764, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14764, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d14764, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20905 (p : Pattern) (guard : d16441 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14759 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20899 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20904 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20906 (p : Pattern) (guard : d16442 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16440 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20894 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16441 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20905 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20907 (p : Pattern) (guard : d1109 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20908 (p : Pattern) (guard : d1110 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20907 p hg
    simpa only [d1110, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d1110, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20909 (p : Pattern) (guard : d1111 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20908 p hg
    simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20910 (p : Pattern) (guard : d1112 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d1112, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20909 p hg
    simpa only [d1112, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20911 (p : Pattern) (guard : d1113 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20910 p hg
    simpa only [d1113, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d1113, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20912 (p : Pattern) (guard : d1120 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20913 (p : Pattern) (guard : d1121 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20912 p hg
    simpa only [d1121, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d1121, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20914 (p : Pattern) (guard : d1122 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20913 p hg
    simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20915 (p : Pattern) (guard : d1123 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d1123, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20914 p hg
    simpa only [d1123, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20916 (p : Pattern) (guard : d1124 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20915 p hg
    simpa only [d1124, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d1124, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20917 (p : Pattern) (guard : d1125 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20911 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20916 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20918 (p : Pattern) (guard : d14765 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14764 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20904 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20919 (p : Pattern) (guard : d16443 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20917 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20918 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20920 (p : Pattern) (guard : d16444 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20906 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16443 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20919 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20921 (p : Pattern) (guard : d16445 p = 1) : d48326 p ≤ (0 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16445, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20392 p hg
    simpa only [d16445, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16444 p = 1 := by simpa only [d16445, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20920 p hg
    simpa only [d16445, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20922 (p : Pattern) (guard : d16446 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16446, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20391 p hg
    simpa only [d16446, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16445 p = 1 := by simpa only [d16446, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20921 p hg
    simpa only [d16446, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20923 (p : Pattern) (guard : d5017 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20924 (p : Pattern) (guard : d5018 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5017 p = 1 := by simpa only [d5018, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20923 p hg
    simpa only [d5018, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5018, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d5018, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20925 (p : Pattern) (guard : d5019 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5018 p = 1 := by simpa only [d5019, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20924 p hg
    simpa only [d5019, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5019, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d5019, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20926 (p : Pattern) (guard : d5020 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5020, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d5020, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5019 p = 1 := by simpa only [d5020, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20925 p hg
    simpa only [d5020, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20927 (p : Pattern) (guard : d5021 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5020 p = 1 := by simpa only [d5021, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20926 p hg
    simpa only [d5021, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5021, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d5021, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20928 (p : Pattern) (guard : d5022 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5021 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20927 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20929 (p : Pattern) (guard : d9843 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20930 (p : Pattern) (guard : d9844 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9843 p = 1 := by simpa only [d9844, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20929 p hg
    simpa only [d9844, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9844, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d9844, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20931 (p : Pattern) (guard : d9846 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9844 p = 1 := by simpa only [d9846, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20930 p hg
    simpa only [d9846, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9846, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d9846, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20932 (p : Pattern) (guard : d14770 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14770, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d14770, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9846 p = 1 := by simpa only [d14770, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20931 p hg
    simpa only [d14770, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20933 (p : Pattern) (guard : d14771 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14770 p = 1 := by simpa only [d14771, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20932 p hg
    simpa only [d14771, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14771, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d14771, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20934 (p : Pattern) (guard : d14772 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14771 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20933 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20935 (p : Pattern) (guard : d14773 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5022 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20928 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20934 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20936 (p : Pattern) (guard : d16447 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20919 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14773 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20935 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20937 (p : Pattern) (guard : d16448 p = 1) : d48326 p ≤ (0 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16448, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20392 p hg
    simpa only [d16448, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16447 p = 1 := by simpa only [d16448, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20936 p hg
    simpa only [d16448, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20938 (p : Pattern) (guard : d16449 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16449, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20391 p hg
    simpa only [d16449, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16448 p = 1 := by simpa only [d16449, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20937 p hg
    simpa only [d16449, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20939 (p : Pattern) (guard : d16450 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16446 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20922 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16449 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20938 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20940 (p : Pattern) (guard : d1127 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20916 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20941 (p : Pattern) (guard : d14778 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20940 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20934 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20942 (p : Pattern) (guard : d16451 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20919 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14778 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20941 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20943 (p : Pattern) (guard : d16452 p = 1) : d48326 p ≤ (0 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16452, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20392 p hg
    simpa only [d16452, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16451 p = 1 := by simpa only [d16452, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20942 p hg
    simpa only [d16452, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20944 (p : Pattern) (guard : d16453 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16453, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20391 p hg
    simpa only [d16453, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16452 p = 1 := by simpa only [d16453, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20943 p hg
    simpa only [d16453, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20945 (p : Pattern) (guard : d16454 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16453 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20944 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20946 (p : Pattern) (guard : d16455 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20939 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16454 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20945 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20947 (p : Pattern) (guard : d16456 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16455 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20946 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20948 (p : Pattern) (guard : d16457 p = 1) : d48338 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16456 p = 1 := by simpa only [d16457, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20947 p hg
    simpa only [d16457, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16457, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d16457, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20949 (p : Pattern) (guard : d16458 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16458, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20390 p hg
    simpa only [d16458, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16457 p = 1 := by simpa only [d16458, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20948 p hg
    simpa only [d16458, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20950 (p : Pattern) (guard : d16459 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16454 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20945 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20951 (p : Pattern) (guard : d16460 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16459 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20950 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20952 (p : Pattern) (guard : d16461 p = 1) : d48338 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16460 p = 1 := by simpa only [d16461, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20951 p hg
    simpa only [d16461, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16461, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d16461, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20953 (p : Pattern) (guard : d16462 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16462, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20390 p hg
    simpa only [d16462, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16461 p = 1 := by simpa only [d16462, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20952 p hg
    simpa only [d16462, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20954 (p : Pattern) (guard : d16463 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16458 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20949 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20953 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20955 (p : Pattern) (guard : d16464 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16463 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20954 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20956 (p : Pattern) (guard : d16465 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16464 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20955 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20957 (p : Pattern) (guard : d16466 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16465 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20956 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20958 (p : Pattern) (guard : d16467 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16462 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20953 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20959 (p : Pattern) (guard : d16468 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16467 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20958 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20960 (p : Pattern) (guard : d16469 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16468 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20959 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20961 (p : Pattern) (guard : d16470 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16469 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20960 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20962 (p : Pattern) (guard : d16471 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16466 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20957 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16470 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20961 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20963 (p : Pattern) (guard : d16472 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16471 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20962 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20964 (p : Pattern) (guard : d16473 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16472 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20963 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20965 (p : Pattern) (guard : d16474 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16473 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20964 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20966 (p : Pattern) (guard : d16475 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16474 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20965 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20967 (p : Pattern) (guard : d16476 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16475 p = 1 := by simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20966 p hg
    simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20968 (p : Pattern) (guard : d16446 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16446, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20426 p hg
    simpa only [d16446, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16445 p = 1 := by simpa only [d16446, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20921 p hg
    simpa only [d16446, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20969 (p : Pattern) (guard : d16449 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16449, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20426 p hg
    simpa only [d16449, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16448 p = 1 := by simpa only [d16449, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20937 p hg
    simpa only [d16449, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20970 (p : Pattern) (guard : d16450 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16446 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20968 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16449 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20969 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20971 (p : Pattern) (guard : d16453 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16453, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20426 p hg
    simpa only [d16453, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16452 p = 1 := by simpa only [d16453, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20943 p hg
    simpa only [d16453, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20972 (p : Pattern) (guard : d16454 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16453 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20971 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20973 (p : Pattern) (guard : d16455 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20970 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16454 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20972 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20974 (p : Pattern) (guard : d16456 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16455 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20973 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20975 (p : Pattern) (guard : d16457 p = 1) : d48329 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16456 p = 1 := by simpa only [d16457, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20974 p hg
    simpa only [d16457, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16457, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d16457, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20976 (p : Pattern) (guard : d16458 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16458, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20425 p hg
    simpa only [d16458, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16457 p = 1 := by simpa only [d16458, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20975 p hg
    simpa only [d16458, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20977 (p : Pattern) (guard : d16459 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16454 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20972 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20978 (p : Pattern) (guard : d16460 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16459 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20977 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20979 (p : Pattern) (guard : d16461 p = 1) : d48329 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16460 p = 1 := by simpa only [d16461, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20978 p hg
    simpa only [d16461, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16461, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d16461, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20980 (p : Pattern) (guard : d16462 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16462, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20425 p hg
    simpa only [d16462, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16461 p = 1 := by simpa only [d16462, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20979 p hg
    simpa only [d16462, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20981 (p : Pattern) (guard : d16463 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16458 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20976 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20980 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20982 (p : Pattern) (guard : d16464 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16463 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20981 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20983 (p : Pattern) (guard : d16465 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16464 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20982 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20984 (p : Pattern) (guard : d16466 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16465 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20983 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20985 (p : Pattern) (guard : d16467 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16462 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20980 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20986 (p : Pattern) (guard : d16468 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16467 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20985 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20987 (p : Pattern) (guard : d16469 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16468 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20986 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20988 (p : Pattern) (guard : d16470 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16469 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20987 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20989 (p : Pattern) (guard : d16471 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16466 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20984 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16470 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20988 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20990 (p : Pattern) (guard : d16472 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16471 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20989 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20991 (p : Pattern) (guard : d16473 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16472 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20990 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20992 (p : Pattern) (guard : d16474 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16473 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20991 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20993 (p : Pattern) (guard : d16475 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16474 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20992 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20994 (p : Pattern) (guard : d16479 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16465 p = 1 := by simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20956 p hg
    simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20995 (p : Pattern) (guard : d16480 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16469 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20960 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20996 (p : Pattern) (guard : d16481 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16479 p = 1 := by simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20994 p hg
    simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16480 p = 1 := by simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20995 p hg
    simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20997 (p : Pattern) (guard : d16482 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16481 p = 1 := by simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20996 p hg
    simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20998 (p : Pattern) (guard : d16483 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16482 p = 1 := by simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20997 p hg
    simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20999 (p : Pattern) (guard : d16484 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16483 p = 1 := by simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20998 p hg
    simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
