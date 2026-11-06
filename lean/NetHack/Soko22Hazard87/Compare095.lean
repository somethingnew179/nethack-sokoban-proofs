import NetHack.Soko22Hazard87.Compare094
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare23750 (p : Pattern) (guard : d179752 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179751 p = 1 := by simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23749 p hg
    simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23751 (p : Pattern) (guard : d179753 p = 1) : d48329 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179752 p = 1 := by simpa only [d179753, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23750 p hg
    simpa only [d179753, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179753, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d179753, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23752 (p : Pattern) (guard : d179754 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179754, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23316 p hg
    simpa only [d179754, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179753 p = 1 := by simpa only [d179754, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23751 p hg
    simpa only [d179754, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23753 (p : Pattern) (guard : d179755 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179750 p = 1 := by simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23748 p hg
    simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23754 (p : Pattern) (guard : d179756 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179755 p = 1 := by simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23753 p hg
    simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23755 (p : Pattern) (guard : d179757 p = 1) : d48329 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179756 p = 1 := by simpa only [d179757, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23754 p hg
    simpa only [d179757, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179757, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d179757, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23756 (p : Pattern) (guard : d179758 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179758, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23316 p hg
    simpa only [d179758, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179757 p = 1 := by simpa only [d179758, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23755 p hg
    simpa only [d179758, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23757 (p : Pattern) (guard : d179759 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179754 p = 1 := by simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23752 p hg
    simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179758 p = 1 := by simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23756 p hg
    simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23758 (p : Pattern) (guard : d179760 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179759 p = 1 := by simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23757 p hg
    simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23759 (p : Pattern) (guard : d179761 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179760 p = 1 := by simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23758 p hg
    simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23760 (p : Pattern) (guard : d179762 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179761 p = 1 := by simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23759 p hg
    simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23761 (p : Pattern) (guard : d179763 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179758 p = 1 := by simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23756 p hg
    simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23762 (p : Pattern) (guard : d179764 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179763 p = 1 := by simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23761 p hg
    simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23763 (p : Pattern) (guard : d179765 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179764 p = 1 := by simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23762 p hg
    simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23764 (p : Pattern) (guard : d179766 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179765 p = 1 := by simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23763 p hg
    simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23765 (p : Pattern) (guard : d179767 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179762 p = 1 := by simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23760 p hg
    simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179766 p = 1 := by simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23764 p hg
    simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23766 (p : Pattern) (guard : d179768 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179767 p = 1 := by simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23765 p hg
    simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23767 (p : Pattern) (guard : d179769 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179768 p = 1 := by simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23766 p hg
    simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23768 (p : Pattern) (guard : d179770 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179769 p = 1 := by simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23767 p hg
    simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23769 (p : Pattern) (guard : d179771 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179770 p = 1 := by simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23768 p hg
    simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23770 (p : Pattern) (guard : d179775 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179761 p = 1 := by simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23733 p hg
    simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23771 (p : Pattern) (guard : d179776 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179765 p = 1 := by simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23737 p hg
    simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23772 (p : Pattern) (guard : d179777 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179775 p = 1 := by simpa only [d179777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23770 p hg
    simpa only [d179777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179776 p = 1 := by simpa only [d179777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23771 p hg
    simpa only [d179777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23773 (p : Pattern) (guard : d179778 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179777 p = 1 := by simpa only [d179778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23772 p hg
    simpa only [d179778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23774 (p : Pattern) (guard : d179779 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179778 p = 1 := by simpa only [d179779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23773 p hg
    simpa only [d179779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23775 (p : Pattern) (guard : d179780 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179779 p = 1 := by simpa only [d179780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23774 p hg
    simpa only [d179780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23776 (p : Pattern) (guard : d179781 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179780 p = 1 := by simpa only [d179781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23775 p hg
    simpa only [d179781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23777 (p : Pattern) (guard : d179782 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179771 p = 1 := by simpa only [d179782, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23769 p hg
    simpa only [d179782, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179781 p = 1 := by simpa only [d179782, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23776 p hg
    simpa only [d179782, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23778 (p : Pattern) (guard : d179783 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179772 p = 1 := by simpa only [d179783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23744 p hg
    simpa only [d179783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179782 p = 1 := by simpa only [d179783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23777 p hg
    simpa only [d179783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23779 (p : Pattern) (guard : d179784 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179783 p = 1 := by simpa only [d179784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23778 p hg
    simpa only [d179784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d179784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23780 (p : Pattern) (guard : d180508 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179784 p = 1 := by simpa only [d180508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23779 p hg
    simpa only [d180508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d180508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23781 (p : Pattern) (guard : d180509 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d180509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180508 p = 1 := by simpa only [d180509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23780 p hg
    simpa only [d180509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23782 (p : Pattern) (guard : d179726 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare23783 (p : Pattern) (guard : d179727 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179726 p = 1 := by simpa only [d179727, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23782 p hg
    simpa only [d179727, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179727, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23352 p hg
    simpa only [d179727, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23784 (p : Pattern) (guard : d179728 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179727 p = 1 := by simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23783 p hg
    simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23785 (p : Pattern) (guard : d179729 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179728 p = 1 := by simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23784 p hg
    simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23786 (p : Pattern) (guard : d179739 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare23787 (p : Pattern) (guard : d179740 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179739 p = 1 := by simpa only [d179740, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23786 p hg
    simpa only [d179740, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179740, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23352 p hg
    simpa only [d179740, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23788 (p : Pattern) (guard : d179741 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179740 p = 1 := by simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23787 p hg
    simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23789 (p : Pattern) (guard : d179742 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179741 p = 1 := by simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23788 p hg
    simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23790 (p : Pattern) (guard : d179743 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179729 p = 1 := by simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23785 p hg
    simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179742 p = 1 := by simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23789 p hg
    simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23791 (p : Pattern) (guard : d179744 p = 1) : d48346 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179744, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23349 p hg
    simpa only [d179744, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179743 p = 1 := by simpa only [d179744, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23790 p hg
    simpa only [d179744, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23792 (p : Pattern) (guard : d179745 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179745, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23348 p hg
    simpa only [d179745, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179744 p = 1 := by simpa only [d179745, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23791 p hg
    simpa only [d179745, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23793 (p : Pattern) (guard : d179746 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179742 p = 1 := by simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23789 p hg
    simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23794 (p : Pattern) (guard : d179747 p = 1) : d48346 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179747, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23349 p hg
    simpa only [d179747, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179746 p = 1 := by simpa only [d179747, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23793 p hg
    simpa only [d179747, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23795 (p : Pattern) (guard : d179748 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179748, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23348 p hg
    simpa only [d179748, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179747 p = 1 := by simpa only [d179748, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23794 p hg
    simpa only [d179748, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23796 (p : Pattern) (guard : d179749 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179745 p = 1 := by simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23792 p hg
    simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179748 p = 1 := by simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23795 p hg
    simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23797 (p : Pattern) (guard : d179750 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179748 p = 1 := by simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23795 p hg
    simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23798 (p : Pattern) (guard : d179751 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179749 p = 1 := by simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23796 p hg
    simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179750 p = 1 := by simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23797 p hg
    simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23799 (p : Pattern) (guard : d179752 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179751 p = 1 := by simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23798 p hg
    simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23800 (p : Pattern) (guard : d179753 p = 1) : d48356 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179752 p = 1 := by simpa only [d179753, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23799 p hg
    simpa only [d179753, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179753, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23363 p hg
    simpa only [d179753, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23801 (p : Pattern) (guard : d179754 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179754, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23347 p hg
    simpa only [d179754, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179753 p = 1 := by simpa only [d179754, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23800 p hg
    simpa only [d179754, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23802 (p : Pattern) (guard : d179755 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179750 p = 1 := by simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23797 p hg
    simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23803 (p : Pattern) (guard : d179756 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179755 p = 1 := by simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23802 p hg
    simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23804 (p : Pattern) (guard : d179757 p = 1) : d48356 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179756 p = 1 := by simpa only [d179757, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23803 p hg
    simpa only [d179757, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179757, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23363 p hg
    simpa only [d179757, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23805 (p : Pattern) (guard : d179758 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179758, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23347 p hg
    simpa only [d179758, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179757 p = 1 := by simpa only [d179758, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23804 p hg
    simpa only [d179758, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23806 (p : Pattern) (guard : d179759 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179754 p = 1 := by simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23801 p hg
    simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179758 p = 1 := by simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23805 p hg
    simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23807 (p : Pattern) (guard : d179760 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179759 p = 1 := by simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23806 p hg
    simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23808 (p : Pattern) (guard : d179761 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179760 p = 1 := by simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23807 p hg
    simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23809 (p : Pattern) (guard : d179775 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179761 p = 1 := by simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23808 p hg
    simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23810 (p : Pattern) (guard : d179763 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179758 p = 1 := by simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23805 p hg
    simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23811 (p : Pattern) (guard : d179764 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179763 p = 1 := by simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23810 p hg
    simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23812 (p : Pattern) (guard : d179765 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179764 p = 1 := by simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23811 p hg
    simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23813 (p : Pattern) (guard : d179776 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179765 p = 1 := by simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23812 p hg
    simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23814 (p : Pattern) (guard : d179777 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179775 p = 1 := by simpa only [d179777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23809 p hg
    simpa only [d179777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179776 p = 1 := by simpa only [d179777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23813 p hg
    simpa only [d179777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23815 (p : Pattern) (guard : d179778 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179777 p = 1 := by simpa only [d179778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23814 p hg
    simpa only [d179778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23816 (p : Pattern) (guard : d179779 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179778 p = 1 := by simpa only [d179779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23815 p hg
    simpa only [d179779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23817 (p : Pattern) (guard : d179780 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179779 p = 1 := by simpa only [d179780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23816 p hg
    simpa only [d179780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23818 (p : Pattern) (guard : d179781 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179780 p = 1 := by simpa only [d179781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23817 p hg
    simpa only [d179781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23819 (p : Pattern) (guard : d180510 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180510, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180510, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179781 p = 1 := by simpa only [d180510, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23818 p hg
    simpa only [d180510, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23820 (p : Pattern) (guard : d180511 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180510 p = 1 := by simpa only [d180511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23819 p hg
    simpa only [d180511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23821 (p : Pattern) (guard : d180512 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180511 p = 1 := by simpa only [d180512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23820 p hg
    simpa only [d180512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23822 (p : Pattern) (guard : d180513 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180512 p = 1 := by simpa only [d180513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23821 p hg
    simpa only [d180513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23823 (p : Pattern) (guard : d180514 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d180513 p = 1 := by simpa only [d180514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23822 p hg
    simpa only [d180514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23824 (p : Pattern) (guard : d180515 p = 1) : d48359 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d180509 p = 1 := by simpa only [d180515, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23781 p hg
    simpa only [d180515, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180514 p = 1 := by simpa only [d180515, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23823 p hg
    simpa only [d180515, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23825 (p : Pattern) (guard : d179896 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare23826 (p : Pattern) (guard : d179897 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179896 p = 1 := by simpa only [d179897, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23825 p hg
    simpa only [d179897, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179897, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23387 p hg
    simpa only [d179897, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23827 (p : Pattern) (guard : d179898 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179897 p = 1 := by simpa only [d179898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23826 p hg
    simpa only [d179898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23828 (p : Pattern) (guard : d179899 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179898 p = 1 := by simpa only [d179899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23827 p hg
    simpa only [d179899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23829 (p : Pattern) (guard : d179909 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare23830 (p : Pattern) (guard : d179910 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179909 p = 1 := by simpa only [d179910, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23829 p hg
    simpa only [d179910, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179910, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23387 p hg
    simpa only [d179910, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23831 (p : Pattern) (guard : d179911 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179910 p = 1 := by simpa only [d179911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23830 p hg
    simpa only [d179911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23832 (p : Pattern) (guard : d179912 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179911 p = 1 := by simpa only [d179912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23831 p hg
    simpa only [d179912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23833 (p : Pattern) (guard : d179913 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179899 p = 1 := by simpa only [d179913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23828 p hg
    simpa only [d179913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179912 p = 1 := by simpa only [d179913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23832 p hg
    simpa only [d179913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23834 (p : Pattern) (guard : d179914 p = 1) : d48362 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179914, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23384 p hg
    simpa only [d179914, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179913 p = 1 := by simpa only [d179914, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23833 p hg
    simpa only [d179914, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23835 (p : Pattern) (guard : d179915 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179915, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23383 p hg
    simpa only [d179915, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179914 p = 1 := by simpa only [d179915, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23834 p hg
    simpa only [d179915, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23836 (p : Pattern) (guard : d179916 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179912 p = 1 := by simpa only [d179916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23832 p hg
    simpa only [d179916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23837 (p : Pattern) (guard : d179917 p = 1) : d48362 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179917, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23384 p hg
    simpa only [d179917, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179916 p = 1 := by simpa only [d179917, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23836 p hg
    simpa only [d179917, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23838 (p : Pattern) (guard : d179918 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179918, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23383 p hg
    simpa only [d179918, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179917 p = 1 := by simpa only [d179918, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23837 p hg
    simpa only [d179918, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23839 (p : Pattern) (guard : d179919 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179915 p = 1 := by simpa only [d179919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23835 p hg
    simpa only [d179919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179918 p = 1 := by simpa only [d179919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23838 p hg
    simpa only [d179919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23840 (p : Pattern) (guard : d179924 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179918 p = 1 := by simpa only [d179924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23838 p hg
    simpa only [d179924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d179924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23841 (p : Pattern) (guard : d179925 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179919 p = 1 := by simpa only [d179925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23839 p hg
    simpa only [d179925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179924 p = 1 := by simpa only [d179925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23840 p hg
    simpa only [d179925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23842 (p : Pattern) (guard : d179926 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179925 p = 1 := by simpa only [d179926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23841 p hg
    simpa only [d179926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d179926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23843 (p : Pattern) (guard : d179927 p = 1) : d48365 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179926 p = 1 := by simpa only [d179927, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23842 p hg
    simpa only [d179927, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179927, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23398 p hg
    simpa only [d179927, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23844 (p : Pattern) (guard : d179928 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179928, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d179928, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179927 p = 1 := by simpa only [d179928, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23843 p hg
    simpa only [d179928, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23845 (p : Pattern) (guard : d179933 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179924 p = 1 := by simpa only [d179933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23840 p hg
    simpa only [d179933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d179933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23846 (p : Pattern) (guard : d179934 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179933 p = 1 := by simpa only [d179934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23845 p hg
    simpa only [d179934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d179934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23847 (p : Pattern) (guard : d179935 p = 1) : d48365 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179934 p = 1 := by simpa only [d179935, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23846 p hg
    simpa only [d179935, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179935, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23398 p hg
    simpa only [d179935, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23848 (p : Pattern) (guard : d179936 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179936, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d179936, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179935 p = 1 := by simpa only [d179936, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23847 p hg
    simpa only [d179936, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23849 (p : Pattern) (guard : d179937 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179928 p = 1 := by simpa only [d179937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23844 p hg
    simpa only [d179937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179936 p = 1 := by simpa only [d179937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23848 p hg
    simpa only [d179937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23850 (p : Pattern) (guard : d179938 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179937 p = 1 := by simpa only [d179938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23849 p hg
    simpa only [d179938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23851 (p : Pattern) (guard : d179939 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179938 p = 1 := by simpa only [d179939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23850 p hg
    simpa only [d179939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23852 (p : Pattern) (guard : d179940 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179939 p = 1 := by simpa only [d179940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23851 p hg
    simpa only [d179940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23853 (p : Pattern) (guard : d179954 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179936 p = 1 := by simpa only [d179954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23848 p hg
    simpa only [d179954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23854 (p : Pattern) (guard : d179955 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179954 p = 1 := by simpa only [d179955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23853 p hg
    simpa only [d179955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23855 (p : Pattern) (guard : d179956 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179955 p = 1 := by simpa only [d179956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23854 p hg
    simpa only [d179956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23856 (p : Pattern) (guard : d179957 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179956 p = 1 := by simpa only [d179957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23855 p hg
    simpa only [d179957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23857 (p : Pattern) (guard : d180516 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179940 p = 1 := by simpa only [d180516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23852 p hg
    simpa only [d180516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179957 p = 1 := by simpa only [d180516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23856 p hg
    simpa only [d180516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23858 (p : Pattern) (guard : d180517 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180516 p = 1 := by simpa only [d180517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23857 p hg
    simpa only [d180517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23859 (p : Pattern) (guard : d180518 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180517 p = 1 := by simpa only [d180518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23858 p hg
    simpa only [d180518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23860 (p : Pattern) (guard : d180519 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180518 p = 1 := by simpa only [d180519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23859 p hg
    simpa only [d180519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23861 (p : Pattern) (guard : d180520 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180519 p = 1 := by simpa only [d180520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23860 p hg
    simpa only [d180520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23862 (p : Pattern) (guard : d180521 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180521, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180521, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180520 p = 1 := by simpa only [d180521, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23861 p hg
    simpa only [d180521, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23863 (p : Pattern) (guard : d180522 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180521 p = 1 := by simpa only [d180522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23862 p hg
    simpa only [d180522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23864 (p : Pattern) (guard : d180523 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180522 p = 1 := by simpa only [d180523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23863 p hg
    simpa only [d180523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23865 (p : Pattern) (guard : d180524 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180523 p = 1 := by simpa only [d180524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23864 p hg
    simpa only [d180524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23866 (p : Pattern) (guard : d180525 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d180524 p = 1 := by simpa only [d180525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23865 p hg
    simpa only [d180525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23867 (p : Pattern) (guard : d180526 p = 1) : d48387 p ≤ (0 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d180525 p = 1 := by simpa only [d180526, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23866 p hg
    simpa only [d180526, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180526, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23415 p hg
    simpa only [d180526, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23868 (p : Pattern) (guard : d180527 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d180515 p = 1 := by simpa only [d180527, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23824 p hg
    simpa only [d180527, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180526 p = 1 := by simpa only [d180527, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23867 p hg
    simpa only [d180527, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23869 (p : Pattern) (guard : d180528 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180527 p = 1 := by simpa only [d180528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23868 p hg
    simpa only [d180528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23870 (p : Pattern) (guard : d180529 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180528 p = 1 := by simpa only [d180529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23869 p hg
    simpa only [d180529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23871 (p : Pattern) (guard : d180530 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180529 p = 1 := by simpa only [d180530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23870 p hg
    simpa only [d180530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23872 (p : Pattern) (guard : d180531 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180530 p = 1 := by simpa only [d180531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23871 p hg
    simpa only [d180531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23873 (p : Pattern) (guard : d180532 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180531 p = 1 := by simpa only [d180532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23872 p hg
    simpa only [d180532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23874 (p : Pattern) (guard : d180533 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180532 p = 1 := by simpa only [d180533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23873 p hg
    simpa only [d180533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23875 (p : Pattern) (guard : d180534 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180533 p = 1 := by simpa only [d180534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23874 p hg
    simpa only [d180534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23876 (p : Pattern) (guard : d180535 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180534 p = 1 := by simpa only [d180535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23875 p hg
    simpa only [d180535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23877 (p : Pattern) (guard : d180536 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180535 p = 1 := by simpa only [d180536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23876 p hg
    simpa only [d180536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23878 (p : Pattern) (guard : d180537 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d180507 p = 1 := by simpa only [d180537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23706 p hg
    simpa only [d180537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180536 p = 1 := by simpa only [d180537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23877 p hg
    simpa only [d180537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23879 (p : Pattern) (guard : d179986 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare23880 (p : Pattern) (guard : d179987 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179986 p = 1 := by simpa only [d179987, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23879 p hg
    simpa only [d179987, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179987, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23292 p hg
    simpa only [d179987, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23881 (p : Pattern) (guard : d179988 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179987 p = 1 := by simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23880 p hg
    simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23882 (p : Pattern) (guard : d179989 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179988 p = 1 := by simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23881 p hg
    simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23883 (p : Pattern) (guard : d179996 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare23884 (p : Pattern) (guard : d179997 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179996 p = 1 := by simpa only [d179997, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23883 p hg
    simpa only [d179997, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179997, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23292 p hg
    simpa only [d179997, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23885 (p : Pattern) (guard : d179998 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179997 p = 1 := by simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23884 p hg
    simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23886 (p : Pattern) (guard : d179999 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179998 p = 1 := by simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23885 p hg
    simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23887 (p : Pattern) (guard : d180000 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179989 p = 1 := by simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23882 p hg
    simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179999 p = 1 := by simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23886 p hg
    simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23888 (p : Pattern) (guard : d180001 p = 1) : d48326 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180001, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23289 p hg
    simpa only [d180001, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180000 p = 1 := by simpa only [d180001, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23887 p hg
    simpa only [d180001, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23889 (p : Pattern) (guard : d180002 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180002, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23288 p hg
    simpa only [d180002, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180001 p = 1 := by simpa only [d180002, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23888 p hg
    simpa only [d180002, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23890 (p : Pattern) (guard : d180003 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179999 p = 1 := by simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23886 p hg
    simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23891 (p : Pattern) (guard : d180004 p = 1) : d48326 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180004, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23289 p hg
    simpa only [d180004, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180003 p = 1 := by simpa only [d180004, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23890 p hg
    simpa only [d180004, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23892 (p : Pattern) (guard : d180005 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180005, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23288 p hg
    simpa only [d180005, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180004 p = 1 := by simpa only [d180005, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23891 p hg
    simpa only [d180005, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23893 (p : Pattern) (guard : d180006 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180002 p = 1 := by simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23889 p hg
    simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180005 p = 1 := by simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23892 p hg
    simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23894 (p : Pattern) (guard : d180007 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180005 p = 1 := by simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23892 p hg
    simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23895 (p : Pattern) (guard : d180008 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180006 p = 1 := by simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23893 p hg
    simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180007 p = 1 := by simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23894 p hg
    simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23896 (p : Pattern) (guard : d180009 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180008 p = 1 := by simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23895 p hg
    simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23897 (p : Pattern) (guard : d180010 p = 1) : d48338 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180009 p = 1 := by simpa only [d180010, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23896 p hg
    simpa only [d180010, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180010, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d180010, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23898 (p : Pattern) (guard : d180011 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180011, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d180011, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180010 p = 1 := by simpa only [d180011, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23897 p hg
    simpa only [d180011, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23899 (p : Pattern) (guard : d180012 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180007 p = 1 := by simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23894 p hg
    simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23900 (p : Pattern) (guard : d180013 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180012 p = 1 := by simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23899 p hg
    simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23901 (p : Pattern) (guard : d180014 p = 1) : d48338 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180013 p = 1 := by simpa only [d180014, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23900 p hg
    simpa only [d180014, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180014, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d180014, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23902 (p : Pattern) (guard : d180015 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180015, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d180015, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180014 p = 1 := by simpa only [d180015, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23901 p hg
    simpa only [d180015, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23903 (p : Pattern) (guard : d180016 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180011 p = 1 := by simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23898 p hg
    simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180015 p = 1 := by simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23902 p hg
    simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23904 (p : Pattern) (guard : d180017 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180016 p = 1 := by simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23903 p hg
    simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23905 (p : Pattern) (guard : d180018 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180017 p = 1 := by simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23904 p hg
    simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23906 (p : Pattern) (guard : d180019 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180018 p = 1 := by simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23905 p hg
    simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23907 (p : Pattern) (guard : d180020 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180015 p = 1 := by simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23902 p hg
    simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23908 (p : Pattern) (guard : d180021 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180020 p = 1 := by simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23907 p hg
    simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23909 (p : Pattern) (guard : d180022 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180021 p = 1 := by simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23908 p hg
    simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23910 (p : Pattern) (guard : d180023 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180022 p = 1 := by simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23909 p hg
    simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23911 (p : Pattern) (guard : d180024 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180019 p = 1 := by simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23906 p hg
    simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180023 p = 1 := by simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23910 p hg
    simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23912 (p : Pattern) (guard : d180025 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180024 p = 1 := by simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23911 p hg
    simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23913 (p : Pattern) (guard : d180026 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180025 p = 1 := by simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23912 p hg
    simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23914 (p : Pattern) (guard : d180027 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180026 p = 1 := by simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23913 p hg
    simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23915 (p : Pattern) (guard : d180028 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180027 p = 1 := by simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23914 p hg
    simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23916 (p : Pattern) (guard : d180029 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180029, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180029, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180028 p = 1 := by simpa only [d180029, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23915 p hg
    simpa only [d180029, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23917 (p : Pattern) (guard : d180002 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180002, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23317 p hg
    simpa only [d180002, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180001 p = 1 := by simpa only [d180002, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23888 p hg
    simpa only [d180002, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23918 (p : Pattern) (guard : d180005 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180005, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23317 p hg
    simpa only [d180005, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180004 p = 1 := by simpa only [d180005, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23891 p hg
    simpa only [d180005, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23919 (p : Pattern) (guard : d180006 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180002 p = 1 := by simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23917 p hg
    simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180005 p = 1 := by simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23918 p hg
    simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23920 (p : Pattern) (guard : d180007 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180005 p = 1 := by simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23918 p hg
    simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23921 (p : Pattern) (guard : d180008 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180006 p = 1 := by simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23919 p hg
    simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180007 p = 1 := by simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23920 p hg
    simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23922 (p : Pattern) (guard : d180009 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180008 p = 1 := by simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23921 p hg
    simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23923 (p : Pattern) (guard : d180010 p = 1) : d48329 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180009 p = 1 := by simpa only [d180010, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23922 p hg
    simpa only [d180010, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180010, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d180010, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23924 (p : Pattern) (guard : d180011 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180011, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23316 p hg
    simpa only [d180011, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180010 p = 1 := by simpa only [d180011, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23923 p hg
    simpa only [d180011, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23925 (p : Pattern) (guard : d180012 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180007 p = 1 := by simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23920 p hg
    simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23926 (p : Pattern) (guard : d180013 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180012 p = 1 := by simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23925 p hg
    simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23927 (p : Pattern) (guard : d180014 p = 1) : d48329 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180013 p = 1 := by simpa only [d180014, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23926 p hg
    simpa only [d180014, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180014, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d180014, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23928 (p : Pattern) (guard : d180015 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180015, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23316 p hg
    simpa only [d180015, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180014 p = 1 := by simpa only [d180015, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23927 p hg
    simpa only [d180015, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23929 (p : Pattern) (guard : d180016 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180011 p = 1 := by simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23924 p hg
    simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180015 p = 1 := by simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23928 p hg
    simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23930 (p : Pattern) (guard : d180017 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180016 p = 1 := by simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23929 p hg
    simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23931 (p : Pattern) (guard : d180018 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180017 p = 1 := by simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23930 p hg
    simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23932 (p : Pattern) (guard : d180019 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180018 p = 1 := by simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23931 p hg
    simpa only [d180019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23933 (p : Pattern) (guard : d180020 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180015 p = 1 := by simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23928 p hg
    simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23934 (p : Pattern) (guard : d180021 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180020 p = 1 := by simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23933 p hg
    simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23935 (p : Pattern) (guard : d180022 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180021 p = 1 := by simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23934 p hg
    simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23936 (p : Pattern) (guard : d180023 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180022 p = 1 := by simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23935 p hg
    simpa only [d180023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23937 (p : Pattern) (guard : d180024 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180019 p = 1 := by simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23932 p hg
    simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180023 p = 1 := by simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23936 p hg
    simpa only [d180024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23938 (p : Pattern) (guard : d180025 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180024 p = 1 := by simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23937 p hg
    simpa only [d180025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23939 (p : Pattern) (guard : d180026 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180025 p = 1 := by simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23938 p hg
    simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23940 (p : Pattern) (guard : d180027 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180026 p = 1 := by simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23939 p hg
    simpa only [d180027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23941 (p : Pattern) (guard : d180028 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180027 p = 1 := by simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23940 p hg
    simpa only [d180028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23942 (p : Pattern) (guard : d180032 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180018 p = 1 := by simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23905 p hg
    simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23943 (p : Pattern) (guard : d180033 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180022 p = 1 := by simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23909 p hg
    simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23944 (p : Pattern) (guard : d180034 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180032 p = 1 := by simpa only [d180034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23942 p hg
    simpa only [d180034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180033 p = 1 := by simpa only [d180034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23943 p hg
    simpa only [d180034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23945 (p : Pattern) (guard : d180035 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180034 p = 1 := by simpa only [d180035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23944 p hg
    simpa only [d180035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23946 (p : Pattern) (guard : d180036 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180035 p = 1 := by simpa only [d180036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23945 p hg
    simpa only [d180036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23947 (p : Pattern) (guard : d180037 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180036 p = 1 := by simpa only [d180037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23946 p hg
    simpa only [d180037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23948 (p : Pattern) (guard : d180038 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d180038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180037 p = 1 := by simpa only [d180038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23947 p hg
    simpa only [d180038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23949 (p : Pattern) (guard : d180039 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d180028 p = 1 := by simpa only [d180039, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23941 p hg
    simpa only [d180039, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180038 p = 1 := by simpa only [d180039, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23948 p hg
    simpa only [d180039, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23950 (p : Pattern) (guard : d180040 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d180029 p = 1 := by simpa only [d180040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23916 p hg
    simpa only [d180040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180039 p = 1 := by simpa only [d180040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23949 p hg
    simpa only [d180040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23951 (p : Pattern) (guard : d180041 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180040 p = 1 := by simpa only [d180041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23950 p hg
    simpa only [d180041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d180041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23952 (p : Pattern) (guard : d180538 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180041 p = 1 := by simpa only [d180538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23951 p hg
    simpa only [d180538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d180538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23953 (p : Pattern) (guard : d180539 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d180539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180538 p = 1 := by simpa only [d180539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23952 p hg
    simpa only [d180539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23954 (p : Pattern) (guard : d179986 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare23955 (p : Pattern) (guard : d179987 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179986 p = 1 := by simpa only [d179987, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23954 p hg
    simpa only [d179987, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179987, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23352 p hg
    simpa only [d179987, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23956 (p : Pattern) (guard : d179988 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179987 p = 1 := by simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23955 p hg
    simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23957 (p : Pattern) (guard : d179989 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179988 p = 1 := by simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23956 p hg
    simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23958 (p : Pattern) (guard : d179996 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare23959 (p : Pattern) (guard : d179997 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179996 p = 1 := by simpa only [d179997, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23958 p hg
    simpa only [d179997, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179997, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23352 p hg
    simpa only [d179997, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23960 (p : Pattern) (guard : d179998 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179997 p = 1 := by simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23959 p hg
    simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23961 (p : Pattern) (guard : d179999 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179998 p = 1 := by simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23960 p hg
    simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23962 (p : Pattern) (guard : d180000 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179989 p = 1 := by simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23957 p hg
    simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179999 p = 1 := by simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23961 p hg
    simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23963 (p : Pattern) (guard : d180001 p = 1) : d48346 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180001, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23349 p hg
    simpa only [d180001, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180000 p = 1 := by simpa only [d180001, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23962 p hg
    simpa only [d180001, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23964 (p : Pattern) (guard : d180002 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180002, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23348 p hg
    simpa only [d180002, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180001 p = 1 := by simpa only [d180002, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23963 p hg
    simpa only [d180002, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23965 (p : Pattern) (guard : d180003 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179999 p = 1 := by simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23961 p hg
    simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23966 (p : Pattern) (guard : d180004 p = 1) : d48346 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180004, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23349 p hg
    simpa only [d180004, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180003 p = 1 := by simpa only [d180004, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23965 p hg
    simpa only [d180004, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23967 (p : Pattern) (guard : d180005 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180005, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23348 p hg
    simpa only [d180005, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180004 p = 1 := by simpa only [d180005, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23966 p hg
    simpa only [d180005, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23968 (p : Pattern) (guard : d180006 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180002 p = 1 := by simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23964 p hg
    simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180005 p = 1 := by simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23967 p hg
    simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23969 (p : Pattern) (guard : d180007 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180005 p = 1 := by simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23967 p hg
    simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23970 (p : Pattern) (guard : d180008 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180006 p = 1 := by simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23968 p hg
    simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180007 p = 1 := by simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23969 p hg
    simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23971 (p : Pattern) (guard : d180009 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180008 p = 1 := by simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23970 p hg
    simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23972 (p : Pattern) (guard : d180010 p = 1) : d48356 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180009 p = 1 := by simpa only [d180010, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23971 p hg
    simpa only [d180010, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180010, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23363 p hg
    simpa only [d180010, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23973 (p : Pattern) (guard : d180011 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180011, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23347 p hg
    simpa only [d180011, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180010 p = 1 := by simpa only [d180011, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23972 p hg
    simpa only [d180011, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23974 (p : Pattern) (guard : d180012 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180007 p = 1 := by simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23969 p hg
    simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23975 (p : Pattern) (guard : d180013 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180012 p = 1 := by simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23974 p hg
    simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23976 (p : Pattern) (guard : d180014 p = 1) : d48356 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180013 p = 1 := by simpa only [d180014, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23975 p hg
    simpa only [d180014, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180014, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23363 p hg
    simpa only [d180014, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23977 (p : Pattern) (guard : d180015 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180015, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23347 p hg
    simpa only [d180015, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180014 p = 1 := by simpa only [d180015, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23976 p hg
    simpa only [d180015, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23978 (p : Pattern) (guard : d180016 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180011 p = 1 := by simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23973 p hg
    simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180015 p = 1 := by simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23977 p hg
    simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23979 (p : Pattern) (guard : d180017 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180016 p = 1 := by simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23978 p hg
    simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23980 (p : Pattern) (guard : d180018 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180017 p = 1 := by simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23979 p hg
    simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23981 (p : Pattern) (guard : d180032 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180018 p = 1 := by simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23980 p hg
    simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23982 (p : Pattern) (guard : d180020 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180015 p = 1 := by simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23977 p hg
    simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23983 (p : Pattern) (guard : d180021 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180020 p = 1 := by simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23982 p hg
    simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23984 (p : Pattern) (guard : d180022 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180021 p = 1 := by simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23983 p hg
    simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23985 (p : Pattern) (guard : d180033 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180022 p = 1 := by simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23984 p hg
    simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23986 (p : Pattern) (guard : d180034 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180032 p = 1 := by simpa only [d180034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23981 p hg
    simpa only [d180034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180033 p = 1 := by simpa only [d180034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23985 p hg
    simpa only [d180034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23987 (p : Pattern) (guard : d180035 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d180035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180034 p = 1 := by simpa only [d180035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23986 p hg
    simpa only [d180035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23988 (p : Pattern) (guard : d180036 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180035 p = 1 := by simpa only [d180036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23987 p hg
    simpa only [d180036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d180036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23989 (p : Pattern) (guard : d180037 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d180037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180036 p = 1 := by simpa only [d180037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23988 p hg
    simpa only [d180037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23990 (p : Pattern) (guard : d180038 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d180038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180037 p = 1 := by simpa only [d180038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23989 p hg
    simpa only [d180038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23991 (p : Pattern) (guard : d180540 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180540, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180540, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180038 p = 1 := by simpa only [d180540, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23990 p hg
    simpa only [d180540, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23992 (p : Pattern) (guard : d180541 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180540 p = 1 := by simpa only [d180541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23991 p hg
    simpa only [d180541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23993 (p : Pattern) (guard : d180542 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180541 p = 1 := by simpa only [d180542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23992 p hg
    simpa only [d180542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23994 (p : Pattern) (guard : d180543 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180542 p = 1 := by simpa only [d180543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23993 p hg
    simpa only [d180543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23995 (p : Pattern) (guard : d180544 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d180543 p = 1 := by simpa only [d180544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23994 p hg
    simpa only [d180544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23996 (p : Pattern) (guard : d180545 p = 1) : d48359 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d180539 p = 1 := by simpa only [d180545, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23953 p hg
    simpa only [d180545, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180544 p = 1 := by simpa only [d180545, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23995 p hg
    simpa only [d180545, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23997 (p : Pattern) (guard : d180137 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare23998 (p : Pattern) (guard : d180138 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d180137 p = 1 := by simpa only [d180138, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23997 p hg
    simpa only [d180138, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180138, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23387 p hg
    simpa only [d180138, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23999 (p : Pattern) (guard : d180139 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d180139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180138 p = 1 := by simpa only [d180139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23998 p hg
    simpa only [d180139, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
