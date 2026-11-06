/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons047
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6720 (p : Pattern) (guard : d4673 p = 1) : d813 p ≤ (2 : Int) + d4687 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d813, d4687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6711 p hg
    simpa only [d813, d4687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d813, d4687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6719 p hg
    simpa only [d813, d4687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6721 (p : Pattern) (guard : d4673 p = 1) : d814 p ≤ (2 : Int) + d4688 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d814, d4688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6702 p hg
    simpa only [d814, d4688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d814, d4688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6720 p hg
    simpa only [d814, d4688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6722 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6723 (p : Pattern) (guard : d4673 p = 1) : d815 p ≤ (2 : Int) + d4681 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d815, d4681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6676 p hg
    simpa only [d4673, d815, d4681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d815, d4681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6722 p hg
    simpa only [d4673, d815, d4681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6724 (p : Pattern) (guard : d4673 p = 1) : d816 p ≤ (2 : Int) + d4683 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d816, d4683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6723 p hg
    simpa only [d816, d4683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d816, d4683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6710 p hg
    simpa only [d816, d4683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6725 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (2 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6726 (p : Pattern) (guard : d4673 p = 1) : d817 p ≤ (2 : Int) + d4684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d817, d4684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6691 p hg
    simpa only [d4673, d817, d4684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d817, d4684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6725 p hg
    simpa only [d4673, d817, d4684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6727 (p : Pattern) (guard : d4673 p = 1) : d818 p ≤ (2 : Int) + d4686 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d818, d4686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6726 p hg
    simpa only [d818, d4686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d818, d4686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6718 p hg
    simpa only [d818, d4686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6728 (p : Pattern) (guard : d4673 p = 1) : d819 p ≤ (2 : Int) + d4687 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d819, d4687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6724 p hg
    simpa only [d819, d4687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d819, d4687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6727 p hg
    simpa only [d819, d4687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6729 (p : Pattern) (guard : d0 p = 1) : d89 p ≤ (2 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6730 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6731 (p : Pattern) (guard : d4148 p = 1) : d63 p ≤ (2 : Int) + d62 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6164 p hg
    simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6730 p hg
    simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6732 (p : Pattern) (guard : d4672 p = 1) : d90 p ≤ (2 : Int) + d62 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6729 p hg
    simpa only [d4672, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6731 p hg
    simpa only [d4672, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6733 (p : Pattern) (guard : d4673 p = 1) : d820 p ≤ (2 : Int) + d4689 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d820, d4689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6732 p hg
    simpa only [d4673, d820, d4689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d820, d4689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4673, d820, d4689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6734 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6735 (p : Pattern) (guard : d4148 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare6736 (p : Pattern) (guard : d4672 p = 1) : d91 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6734 p hg
    simpa only [d4672, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6735 p hg
    simpa only [d4672, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6737 (p : Pattern) (guard : d4673 p = 1) : d93 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6736 p hg
    simpa only [d4673, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4673, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6738 (p : Pattern) (guard : d4673 p = 1) : d821 p ≤ (2 : Int) + d4690 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d821, d4690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6733 p hg
    simpa only [d821, d4690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d821, d4690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6737 p hg
    simpa only [d821, d4690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6739 (p : Pattern) (guard : d4673 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare6740 (p : Pattern) (guard : d4673 p = 1) : d95 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6737 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6739 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6741 (p : Pattern) (guard : d4673 p = 1) : d822 p ≤ (2 : Int) + d4691 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d822, d4691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6738 p hg
    simpa only [d822, d4691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d822, d4691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6740 p hg
    simpa only [d822, d4691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6742 (p : Pattern) (guard : d4673 p = 1) : d823 p ≤ (2 : Int) + d4692 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d823, d4692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6728 p hg
    simpa only [d823, d4692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d823, d4692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6741 p hg
    simpa only [d823, d4692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6743 (p : Pattern) (guard : d4673 p = 1) : d824 p ≤ (2 : Int) + d4693 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d824, d4693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6721 p hg
    simpa only [d824, d4693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d824, d4693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6742 p hg
    simpa only [d824, d4693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6744 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (2 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6745 (p : Pattern) (guard : d4673 p = 1) : d825 p ≤ (2 : Int) + d4674 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d825, d4674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6676 p hg
    simpa only [d4673, d825, d4674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d825, d4674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6744 p hg
    simpa only [d4673, d825, d4674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6746 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d43 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6747 (p : Pattern) (guard : d4673 p = 1) : d826 p ≤ (2 : Int) + d4675 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d826, d4675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6684 p hg
    simpa only [d4673, d826, d4675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d826, d4675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6746 p hg
    simpa only [d4673, d826, d4675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6748 (p : Pattern) (guard : d4673 p = 1) : d827 p ≤ (2 : Int) + d4676 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d827, d4676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6745 p hg
    simpa only [d827, d4676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d827, d4676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6747 p hg
    simpa only [d827, d4676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6749 (p : Pattern) (guard : d0 p = 1) : d394 p ≤ (2 : Int) + d795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6750 (p : Pattern) (guard : d4673 p = 1) : d828 p ≤ (2 : Int) + d4677 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d828, d4677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6691 p hg
    simpa only [d4673, d828, d4677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d828, d4677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6749 p hg
    simpa only [d4673, d828, d4677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6751 (p : Pattern) (guard : d4673 p = 1) : d829 p ≤ (2 : Int) + d4679 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d829, d4679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6750 p hg
    simpa only [d829, d4679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d829, d4679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6700 p hg
    simpa only [d829, d4679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6752 (p : Pattern) (guard : d4673 p = 1) : d830 p ≤ (2 : Int) + d4680 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d830, d4680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6748 p hg
    simpa only [d830, d4680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d830, d4680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6751 p hg
    simpa only [d830, d4680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6753 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6754 (p : Pattern) (guard : d4673 p = 1) : d831 p ≤ (2 : Int) + d4681 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d831, d4681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6676 p hg
    simpa only [d4673, d831, d4681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d831, d4681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6753 p hg
    simpa only [d4673, d831, d4681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6755 (p : Pattern) (guard : d4673 p = 1) : d832 p ≤ (2 : Int) + d4683 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d832, d4683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6754 p hg
    simpa only [d832, d4683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d832, d4683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6710 p hg
    simpa only [d832, d4683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6756 (p : Pattern) (guard : d4673 p = 1) : d833 p ≤ (2 : Int) + d4687 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d833, d4687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6755 p hg
    simpa only [d833, d4687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d833, d4687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6719 p hg
    simpa only [d833, d4687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6757 (p : Pattern) (guard : d4673 p = 1) : d834 p ≤ (2 : Int) + d4688 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d834, d4688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6752 p hg
    simpa only [d834, d4688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d834, d4688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6756 p hg
    simpa only [d834, d4688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6758 (p : Pattern) (guard : d4673 p = 1) : d835 p ≤ (2 : Int) + d4694 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d835, d4694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6756 p hg
    simpa only [d835, d4694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d835, d4694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6739 p hg
    simpa only [d835, d4694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6759 (p : Pattern) (guard : d4673 p = 1) : d836 p ≤ (2 : Int) + d4695 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d836, d4695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6757 p hg
    simpa only [d836, d4695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d836, d4695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6758 p hg
    simpa only [d836, d4695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6760 (p : Pattern) (guard : d4673 p = 1) : d837 p ≤ (2 : Int) + d4696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d837, d4696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6743 p hg
    simpa only [d837, d4696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d837, d4696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6759 p hg
    simpa only [d837, d4696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6761 (p : Pattern) (guard : d0 p = 1) : d372 p ≤ (2 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6762 (p : Pattern) (guard : d4673 p = 1) : d838 p ≤ (2 : Int) + d4674 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d838, d4674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6676 p hg
    simpa only [d4673, d838, d4674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d838, d4674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6761 p hg
    simpa only [d4673, d838, d4674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6763 (p : Pattern) (guard : d4673 p = 1) : d839 p ≤ (2 : Int) + d4676 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d839, d4676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6762 p hg
    simpa only [d839, d4676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d839, d4676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6747 p hg
    simpa only [d839, d4676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6764 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (2 : Int) + d795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6765 (p : Pattern) (guard : d4673 p = 1) : d840 p ≤ (2 : Int) + d4677 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d840, d4677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6691 p hg
    simpa only [d4673, d840, d4677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d840, d4677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6764 p hg
    simpa only [d4673, d840, d4677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6766 (p : Pattern) (guard : d4673 p = 1) : d841 p ≤ (2 : Int) + d4679 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d841, d4679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6765 p hg
    simpa only [d841, d4679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d841, d4679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6700 p hg
    simpa only [d841, d4679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6767 (p : Pattern) (guard : d4673 p = 1) : d842 p ≤ (2 : Int) + d4680 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d842, d4680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6763 p hg
    simpa only [d842, d4680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d842, d4680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6766 p hg
    simpa only [d842, d4680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6768 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6769 (p : Pattern) (guard : d4673 p = 1) : d843 p ≤ (2 : Int) + d4681 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d843, d4681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6676 p hg
    simpa only [d4673, d843, d4681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d843, d4681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6768 p hg
    simpa only [d4673, d843, d4681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6770 (p : Pattern) (guard : d4673 p = 1) : d844 p ≤ (2 : Int) + d4683 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d844, d4683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6769 p hg
    simpa only [d844, d4683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d844, d4683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6710 p hg
    simpa only [d844, d4683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6771 (p : Pattern) (guard : d4673 p = 1) : d845 p ≤ (2 : Int) + d4687 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d845, d4687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6770 p hg
    simpa only [d845, d4687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d845, d4687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6719 p hg
    simpa only [d845, d4687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6772 (p : Pattern) (guard : d4673 p = 1) : d846 p ≤ (2 : Int) + d4688 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d846, d4688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6767 p hg
    simpa only [d846, d4688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d846, d4688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6771 p hg
    simpa only [d846, d4688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6773 (p : Pattern) (guard : d4673 p = 1) : d847 p ≤ (2 : Int) + d4692 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d847, d4692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6720 p hg
    simpa only [d847, d4692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d847, d4692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6741 p hg
    simpa only [d847, d4692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6774 (p : Pattern) (guard : d4673 p = 1) : d848 p ≤ (2 : Int) + d4693 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d848, d4693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6772 p hg
    simpa only [d848, d4693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d848, d4693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6773 p hg
    simpa only [d848, d4693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6775 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (2 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6776 (p : Pattern) (guard : d4673 p = 1) : d815 p ≤ (2 : Int) + d4674 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d815, d4674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6676 p hg
    simpa only [d4673, d815, d4674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d815, d4674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6775 p hg
    simpa only [d4673, d815, d4674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6777 (p : Pattern) (guard : d4673 p = 1) : d849 p ≤ (2 : Int) + d4676 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d849, d4676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6776 p hg
    simpa only [d849, d4676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d849, d4676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6747 p hg
    simpa only [d849, d4676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6778 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (2 : Int) + d795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6779 (p : Pattern) (guard : d4673 p = 1) : d817 p ≤ (2 : Int) + d4677 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d817, d4677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6691 p hg
    simpa only [d4673, d817, d4677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d817, d4677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6778 p hg
    simpa only [d4673, d817, d4677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6780 (p : Pattern) (guard : d4673 p = 1) : d850 p ≤ (2 : Int) + d4679 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d850, d4679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6779 p hg
    simpa only [d850, d4679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d850, d4679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6700 p hg
    simpa only [d850, d4679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6781 (p : Pattern) (guard : d4673 p = 1) : d851 p ≤ (2 : Int) + d4680 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d851, d4680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6777 p hg
    simpa only [d851, d4680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d851, d4680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6780 p hg
    simpa only [d851, d4680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6782 (p : Pattern) (guard : d4673 p = 1) : d852 p ≤ (2 : Int) + d4688 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d852, d4688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6781 p hg
    simpa only [d852, d4688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d852, d4688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6756 p hg
    simpa only [d852, d4688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6783 (p : Pattern) (guard : d4673 p = 1) : d853 p ≤ (2 : Int) + d4695 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d853, d4695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6782 p hg
    simpa only [d853, d4695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d853, d4695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6758 p hg
    simpa only [d853, d4695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6784 (p : Pattern) (guard : d4673 p = 1) : d854 p ≤ (2 : Int) + d4696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d854, d4696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6774 p hg
    simpa only [d854, d4696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d854, d4696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6783 p hg
    simpa only [d854, d4696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6785 (p : Pattern) (guard : d4673 p = 1) : d855 p ≤ (2 : Int) + d4696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6760 p hg
    simpa only [d855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6784 p hg
    simpa only [d855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6786 (p : Pattern) (guard : d0 p = 1) : d105 p ≤ (2 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6787 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (2 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6788 (p : Pattern) (guard : d4148 p = 1) : d110 p ≤ (2 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2199 p hg
    simpa only [d4148, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6787 p hg
    simpa only [d4148, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6789 (p : Pattern) (guard : d4672 p = 1) : d111 p ≤ (2 : Int) + d105 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6786 p hg
    simpa only [d4672, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6788 p hg
    simpa only [d4672, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6790 (p : Pattern) (guard : d0 p = 1) : d372 p ≤ (2 : Int) + d118 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6791 (p : Pattern) (guard : d4673 p = 1) : d856 p ≤ (2 : Int) + d4697 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d856, d4697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6789 p hg
    simpa only [d4673, d856, d4697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d856, d4697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6790 p hg
    simpa only [d4673, d856, d4697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6792 (p : Pattern) (guard : d0 p = 1) : d118 p ≤ (2 : Int) + d118 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6793 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (2 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2159 p hg
    simpa only [d132, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2161 p hg
    simpa only [d132, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6794 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (2 : Int) + d118 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6795 (p : Pattern) (guard : d4148 p = 1) : d149 p ≤ (2 : Int) + d118 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6793 p hg
    simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6794 p hg
    simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6796 (p : Pattern) (guard : d4672 p = 1) : d857 p ≤ (2 : Int) + d118 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6792 p hg
    simpa only [d4672, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6795 p hg
    simpa only [d4672, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6797 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6798 (p : Pattern) (guard : d4673 p = 1) : d858 p ≤ (2 : Int) + d4698 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d858, d4698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6796 p hg
    simpa only [d4673, d858, d4698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d858, d4698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6797 p hg
    simpa only [d4673, d858, d4698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6799 (p : Pattern) (guard : d4673 p = 1) : d859 p ≤ (2 : Int) + d4699 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d859, d4699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6791 p hg
    simpa only [d859, d4699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d859, d4699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6798 p hg
    simpa only [d859, d4699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6800 (p : Pattern) (guard : d0 p = 1) : d133 p ≤ (2 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6801 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (2 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6802 (p : Pattern) (guard : d4148 p = 1) : d134 p ≤ (2 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6163 p hg
    simpa only [d4148, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6801 p hg
    simpa only [d4148, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6803 (p : Pattern) (guard : d4672 p = 1) : d135 p ≤ (2 : Int) + d132 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6800 p hg
    simpa only [d4672, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6802 p hg
    simpa only [d4672, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6804 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (2 : Int) + d861 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6805 (p : Pattern) (guard : d4673 p = 1) : d860 p ≤ (2 : Int) + d4700 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d860, d4700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6803 p hg
    simpa only [d4673, d860, d4700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d860, d4700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6804 p hg
    simpa only [d4673, d860, d4700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6806 (p : Pattern) (guard : d0 p = 1) : d862 p ≤ (2 : Int) + d861 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6807 (p : Pattern) (guard : d1 p = 1) : d234 p ≤ (2 : Int) + d861 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d234, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2189 p hg
    simpa only [d234, d861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d234, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d234, d861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6808 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d861 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6809 (p : Pattern) (guard : d4148 p = 1) : d863 p ≤ (2 : Int) + d861 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6807 p hg
    simpa only [d4148, d863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6808 p hg
    simpa only [d4148, d863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6810 (p : Pattern) (guard : d4672 p = 1) : d864 p ≤ (2 : Int) + d861 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6806 p hg
    simpa only [d4672, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6809 p hg
    simpa only [d4672, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6811 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d229 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6812 (p : Pattern) (guard : d4673 p = 1) : d865 p ≤ (2 : Int) + d4701 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d865, d4701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6810 p hg
    simpa only [d4673, d865, d4701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d865, d4701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6811 p hg
    simpa only [d4673, d865, d4701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6813 (p : Pattern) (guard : d4673 p = 1) : d866 p ≤ (2 : Int) + d4702 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d866, d4702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6805 p hg
    simpa only [d866, d4702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d866, d4702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6812 p hg
    simpa only [d866, d4702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6814 (p : Pattern) (guard : d4673 p = 1) : d867 p ≤ (2 : Int) + d4703 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d867, d4703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6799 p hg
    simpa only [d867, d4703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d867, d4703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6813 p hg
    simpa only [d867, d4703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6815 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (2 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6816 (p : Pattern) (guard : d4673 p = 1) : d868 p ≤ (2 : Int) + d4704 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d868, d4704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6789 p hg
    simpa only [d4673, d868, d4704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d868, d4704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6815 p hg
    simpa only [d4673, d868, d4704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6817 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (2 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6818 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (2 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6819 (p : Pattern) (guard : d4148 p = 1) : d149 p ≤ (2 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5514 p hg
    simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6818 p hg
    simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6820 (p : Pattern) (guard : d4672 p = 1) : d869 p ≤ (2 : Int) + d132 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6817 p hg
    simpa only [d4672, d869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6819 p hg
    simpa only [d4672, d869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6821 (p : Pattern) (guard : d4673 p = 1) : d870 p ≤ (2 : Int) + d4705 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d870, d4705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6820 p hg
    simpa only [d4673, d870, d4705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d870, d4705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4673, d870, d4705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6822 (p : Pattern) (guard : d4673 p = 1) : d871 p ≤ (2 : Int) + d4706 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d871, d4706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6816 p hg
    simpa only [d871, d4706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d871, d4706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6821 p hg
    simpa only [d871, d4706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6823 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6824 (p : Pattern) (guard : d4673 p = 1) : d872 p ≤ (2 : Int) + d4707 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d872, d4707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6803 p hg
    simpa only [d4673, d872, d4707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d872, d4707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6823 p hg
    simpa only [d4673, d872, d4707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6825 (p : Pattern) (guard : d0 p = 1) : d873 p ≤ (2 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6826 (p : Pattern) (guard : d4148 p = 1) : d153 p ≤ (2 : Int) + d109 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4807 p hg
    simpa only [d4148, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6823 p hg
    simpa only [d4148, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6827 (p : Pattern) (guard : d4672 p = 1) : d874 p ≤ (2 : Int) + d109 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6825 p hg
    simpa only [d4672, d874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6826 p hg
    simpa only [d4672, d874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6828 (p : Pattern) (guard : d4673 p = 1) : d875 p ≤ (2 : Int) + d4708 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d875, d4708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6827 p hg
    simpa only [d4673, d875, d4708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d875, d4708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4673, d875, d4708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6829 (p : Pattern) (guard : d4673 p = 1) : d876 p ≤ (2 : Int) + d4709 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d876, d4709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6824 p hg
    simpa only [d876, d4709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d876, d4709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6828 p hg
    simpa only [d876, d4709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6830 (p : Pattern) (guard : d4673 p = 1) : d877 p ≤ (2 : Int) + d4710 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d877, d4710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6822 p hg
    simpa only [d877, d4710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d877, d4710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6829 p hg
    simpa only [d877, d4710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6831 (p : Pattern) (guard : d4673 p = 1) : d878 p ≤ (2 : Int) + d4711 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d878, d4711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6814 p hg
    simpa only [d878, d4711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d878, d4711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6830 p hg
    simpa only [d878, d4711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6832 (p : Pattern) (guard : d0 p = 1) : d394 p ≤ (2 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6833 (p : Pattern) (guard : d4673 p = 1) : d879 p ≤ (2 : Int) + d4704 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d879, d4704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6789 p hg
    simpa only [d4673, d879, d4704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d879, d4704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6832 p hg
    simpa only [d4673, d879, d4704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6834 (p : Pattern) (guard : d4673 p = 1) : d880 p ≤ (2 : Int) + d4706 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d880, d4706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6833 p hg
    simpa only [d880, d4706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d880, d4706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6821 p hg
    simpa only [d880, d4706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6835 (p : Pattern) (guard : d4673 p = 1) : d881 p ≤ (2 : Int) + d4710 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d881, d4710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6834 p hg
    simpa only [d881, d4710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d881, d4710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6829 p hg
    simpa only [d881, d4710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6836 (p : Pattern) (guard : d0 p = 1) : d112 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6837 (p : Pattern) (guard : d4672 p = 1) : d159 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6836 p hg
    simpa only [d4672, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6735 p hg
    simpa only [d4672, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6838 (p : Pattern) (guard : d4673 p = 1) : d160 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6837 p hg
    simpa only [d4673, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4673, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6839 (p : Pattern) (guard : d4673 p = 1) : d161 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6838 p hg
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6739 p hg
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6840 (p : Pattern) (guard : d4673 p = 1) : d162 p ≤ (2 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6839 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6739 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6841 (p : Pattern) (guard : d4673 p = 1) : d882 p ≤ (2 : Int) + d4712 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d882, d4712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6835 p hg
    simpa only [d882, d4712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d882, d4712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6840 p hg
    simpa only [d882, d4712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6842 (p : Pattern) (guard : d4673 p = 1) : d883 p ≤ (2 : Int) + d4713 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d883, d4713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6831 p hg
    simpa only [d883, d4713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d883, d4713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6841 p hg
    simpa only [d883, d4713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6843 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (2 : Int) + d118 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6844 (p : Pattern) (guard : d4673 p = 1) : d884 p ≤ (2 : Int) + d4697 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d884, d4697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6789 p hg
    simpa only [d4673, d884, d4697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d884, d4697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6843 p hg
    simpa only [d4673, d884, d4697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6845 (p : Pattern) (guard : d4673 p = 1) : d885 p ≤ (2 : Int) + d4699 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d885, d4699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6844 p hg
    simpa only [d885, d4699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d885, d4699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6798 p hg
    simpa only [d885, d4699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6846 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (2 : Int) + d861 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6847 (p : Pattern) (guard : d4673 p = 1) : d886 p ≤ (2 : Int) + d4700 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d886, d4700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6803 p hg
    simpa only [d4673, d886, d4700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d886, d4700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6846 p hg
    simpa only [d4673, d886, d4700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6848 (p : Pattern) (guard : d4673 p = 1) : d887 p ≤ (2 : Int) + d4702 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d887, d4702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6847 p hg
    simpa only [d887, d4702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d887, d4702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6812 p hg
    simpa only [d887, d4702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6849 (p : Pattern) (guard : d4673 p = 1) : d888 p ≤ (2 : Int) + d4703 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d888, d4703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6845 p hg
    simpa only [d888, d4703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d888, d4703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6848 p hg
    simpa only [d888, d4703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6850 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6851 (p : Pattern) (guard : d4673 p = 1) : d889 p ≤ (2 : Int) + d4704 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d889, d4704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6789 p hg
    simpa only [d4673, d889, d4704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d889, d4704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6850 p hg
    simpa only [d4673, d889, d4704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6852 (p : Pattern) (guard : d4673 p = 1) : d890 p ≤ (2 : Int) + d4706 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d890, d4706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6851 p hg
    simpa only [d890, d4706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d890, d4706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6821 p hg
    simpa only [d890, d4706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6853 (p : Pattern) (guard : d4673 p = 1) : d891 p ≤ (2 : Int) + d4710 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d891, d4710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6852 p hg
    simpa only [d891, d4710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d891, d4710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6829 p hg
    simpa only [d891, d4710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6854 (p : Pattern) (guard : d4673 p = 1) : d892 p ≤ (2 : Int) + d4711 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d892, d4711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6849 p hg
    simpa only [d892, d4711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d892, d4711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6853 p hg
    simpa only [d892, d4711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6855 (p : Pattern) (guard : d4673 p = 1) : d893 p ≤ (2 : Int) + d4712 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d893, d4712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6853 p hg
    simpa only [d893, d4712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d893, d4712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6739 p hg
    simpa only [d893, d4712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6856 (p : Pattern) (guard : d4673 p = 1) : d894 p ≤ (2 : Int) + d4713 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d894, d4713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6854 p hg
    simpa only [d894, d4713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d894, d4713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6855 p hg
    simpa only [d894, d4713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6857 (p : Pattern) (guard : d4673 p = 1) : d895 p ≤ (2 : Int) + d4713 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6842 p hg
    simpa only [d895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6856 p hg
    simpa only [d895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6858 (p : Pattern) (guard : d4673 p = 1) : d896 p ≤ (2 : Int) + d4714 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d896, d4714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6760 p hg
    simpa only [d896, d4714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d896, d4714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6857 p hg
    simpa only [d896, d4714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6859 (p : Pattern) (guard : d4673 p = 1) : d897 p ≤ (2 : Int) + d4715 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d897, d4715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6785 p hg
    simpa only [d897, d4715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d897, d4715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6858 p hg
    simpa only [d897, d4715, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
